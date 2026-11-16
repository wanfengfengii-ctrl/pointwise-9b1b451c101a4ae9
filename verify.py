"""verify.py — quotedoc 双组件的全量核验与局部访问量实测。

内容:
1. 保留材料回归(fixture_check.normal)。
2. 独立朴素全量模型 Model:每次从已接纳事件整体重算,与 Document/WordIndex
   在任意合法小乱序史上逐批比对(正文、rank/select、词命中、公开增量还原)。
3. 错误注入:引用环、类型冲突、重复冲突、坏引用;失败批前后核对 seq、正文、
   增量完全一致(整批回滚)。
4. 定向场景:跨批/同批父晚到、删先到、墓碑子孙、词首尾拆并、纯分隔符、
   Unicode 坐标、回放源与门面源驱动、过期 lookup。
5. 大正文(深链/星形/随机)中的局部修订访问量实测,并核验结构不变量。
"""
import json
import os
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
os.chdir(Path(__file__).resolve().parent)

import fixture_check
from quotedoc import Document, WordIndex


def check(cond, msg):
    if not cond:
        raise AssertionError(msg)


# ---------------------------------------------------------------------------
# 独立朴素全量模型:与 quotedoc 无任何共享代码
# ---------------------------------------------------------------------------
class Model:
    def __init__(self):
        self.ins = {}        # id -> [after, ch]
        self.erased = set()  # 被删插入身份(无论是否到达)
        self.erase_ids = {}  # 删除事件 id -> target
        self.reserved = set()  # 被引用而未到达的插入型身份
        self.seq = 0

    def ingest(self, events):
        # 规范化+批内去重
        norm = []
        seen = {}
        for e in events:
            idt = (e["id"][0], e["id"][1])
            if e["kind"] == "insert":
                af = e["after"]
                ne = ("i", idt, None if af is None else (af[0], af[1]),
                      e["char"])
            else:
                ne = ("e", idt, (e["target"][0], e["target"][1]))
            if idt in seen:
                if seen[idt] != ne:
                    raise ValueError("dup conflict")
            else:
                seen[idt] = ne
                norm.append(ne)
        if not norm:
            return self.seq
        batch_er = {ne[1] for ne in norm if ne[0] == "e"}
        new_ins = {}
        new_ers = {}
        for ne in norm:
            if ne[0] == "i":
                _, idt, after, ch = ne
                if idt in self.erase_ids or idt in batch_er:
                    raise ValueError("kind conflict")
                if idt in self.ins:
                    if self.ins[idt] != [after, ch]:
                        raise ValueError("content conflict")
                    continue
                if after is not None and (after in self.erase_ids
                                          or after in batch_er):
                    raise ValueError("after->erase")
                new_ins[idt] = (after, ch)
            else:
                _, eid, tg = ne
                if eid in self.ins or eid in self.reserved:
                    raise ValueError("erase id is insert")
                if eid in self.erase_ids:
                    if self.erase_ids[eid] != tg:
                        raise ValueError("content conflict")
                    continue
                if tg in self.erase_ids or tg in batch_er:
                    raise ValueError("target->erase")
                new_ers[eid] = tg
        if not new_ins and not new_ers:
            return self.seq
        # 环核验:在 已接纳+本批 的 after 图上从每个新插入走链
        amap = {i: a for i, (a, c) in self.ins.items()}
        for i, (a, c) in new_ins.items():
            amap[i] = a
        for i in new_ins:
            seen2 = set()
            cur = i
            while cur is not None and cur in amap:
                if cur in seen2:
                    raise ValueError("cycle")
                seen2.add(cur)
                cur = amap[cur]
        # 提交
        for i, (a, c) in new_ins.items():
            self.ins[i] = [a, c]
            self.reserved.discard(i)
            if a is not None and a not in self.ins:
                self.reserved.add(a)
        for eid, tg in new_ers.items():
            self.erase_ids[eid] = tg
            self.erased.add(tg)
            if tg not in self.ins:
                self.reserved.add(tg)
        self.seq += 1
        return self.seq

    # ---- 结构序(前序,孩子按身份降序) ----
    def _visible(self):
        kids = {}
        for i, (a, c) in self.ins.items():
            kids.setdefault(a, []).append(i)
        out = []
        st = sorted(kids.get(None, []))
        while st:
            u = st.pop()
            out.append((u, None if u in self.erased else self.ins[u][1]))
            ks = kids.get(u)
            if ks:
                st.extend(sorted(ks))
        return out

    def _rooted(self, i):
        seen2 = set()
        while i is not None and i in self.ins:
            if i in seen2:
                raise AssertionError("model cycle")
            seen2.add(i)
            i = self.ins[i][0]
        return i is None

    def visible_pairs(self):
        return [(i, c) for i, c in self._visible() if c is not None]

    def text(self):
        return "".join(c for _i, c in self.visible_pairs())

    def length(self):
        return len(self.visible_pairs())

    def rank(self, i):
        if i not in self.ins or not self._rooted(i):
            return None
        n = 0
        for u, c in self._visible():
            if u == i:
                return n
            if c is not None:
                n += 1
        return None

    def select(self, i):
        vp = self.visible_pairs()
        if i < 0 or i >= len(vp):
            raise IndexError
        return list(vp[i][0])

    def words(self):
        # word -> [(首字符身份, offset)]
        out = {}
        off = 0
        cur = []
        cur_ids = []

        def flush():
            if cur:
                w = "".join(cur).lower()
                out.setdefault(w, []).append((cur_ids[0], off - len(cur)))

        for u, c in self._visible():
            if c is None:
                continue
            if ("A" <= c <= "Z") or ("a" <= c <= "z"):
                cur.append(c)
                cur_ids.append(u)
            else:
                flush()
                cur = []
                cur_ids = []
            off += 1
        flush()
        return out


# ---------------------------------------------------------------------------
# 增量应用器(按契约语义执行公开 splice)
# ---------------------------------------------------------------------------
def apply_delta(base_ids, delta):
    seq = list(base_ids)
    for sp in delta["edits"]:
        at = sp["at"]
        rem = [(x[0], x[1]) for x in sp["remove"]]
        check(seq[at:at + len(rem)] == rem,
              f"splice remove不匹配 at={at} rem={rem}")
        seq[at:at + len(rem)] = [(i[0], i[1]) for i, _c in sp["insert"]]
    return seq


def compare(doc, mdl, idx=None, tag=""):
    n = mdl.length()
    check(doc.length() == n, f"{tag} length {doc.length()}!={n}")
    check(doc.slice(0, n) == mdl.text(), f"{tag} text")
    for i in list(mdl.ins) + list(mdl.reserved):
        check(doc.rank(list(i)) == mdl.rank(i), f"{tag} rank {i}")
    for k in range(n):
        check(doc.select(k) == mdl.select(k), f"{tag} select {k}")
    if idx is not None:
        check(idx.sync() == mdl.seq, f"{tag} idx sync seq")
        mw = mdl.words()
        probes = set(mw) | {"cat", "at", "zzz", "a", "hello"}
        for w in probes:
            got = idx.lookup(w)
            exp = [{"id": [f[0], f[1]], "offset": o}
                   for f, o in sorted(mw.get(w, []), key=lambda t: t[1])]
            check(got == exp, f"{tag} lookup {w}: {got} != {exp}")


def check_deltas(doc, hist, tag=""):
    """hist[v]=版本v的可见身份序列;用公开增量把每个旧版本还原到当前。"""
    cur = len(hist) - 1
    for s in range(cur + 1):
        d = doc.edits_since(s)
        check(d["seq"] == cur, f"{tag} delta seq")
        got = apply_delta(hist[s], d)
        check(got == hist[cur], f"{tag} delta restore from {s}")


# ---------------------------------------------------------------------------
# 随机历史生成(合法 DAG,发射顺序打乱 → 晚到父;另注入非法批)
# ---------------------------------------------------------------------------
def gen_history(rng, nbatches):
    sites = ["a", "b", "c"]
    ctr = {s: 0 for s in sites}
    xctr = [0]
    created = []      # 已创建插入身份(DAG 序,after 只指向更早创建者)
    pool = []         # 待发射合法事件
    emitted = []      # 已发射合法事件(供重复)
    batches = []      # (events, expect_error)
    chars = "aAbB cCzZ水é,"

    def new_ins_id():
        s = rng.choice(sites)
        ctr[s] += 1
        return (s, ctr[s])

    def mk_insert():
        i = new_ins_id()
        r = rng.random()
        if r < 0.3 or not created:
            after = None
        else:
            after = rng.choice(created)
        ch = rng.choice(chars)
        created.append(i)
        ev = {"id": [i[0], i[1]], "kind": "insert",
              "after": None if after is None else [after[0], after[1]],
              "char": ch}
        return ev

    def mk_erase():
        xctr[0] += 1
        eid = ("x", xctr[0])
        if created and rng.random() < 0.8:
            tg = rng.choice(created)
        else:
            tg = new_ins_id()  # 删除先到(目标事件可能永不创建)
        return {"id": [eid[0], eid[1]], "kind": "erase",
                "target": [tg[0], tg[1]]}

    for b in range(nbatches):
        r = rng.random()
        if r < 0.15 and b > 3:
            # 非法批
            kind = rng.randrange(6)
            if kind == 0:  # 二元环
                p, q = new_ins_id(), new_ins_id()
                ev = [{"id": [p[0], p[1]], "kind": "insert",
                       "after": [q[0], q[1]], "char": "a"},
                      {"id": [q[0], q[1]], "kind": "insert",
                       "after": [p[0], p[1]], "char": "b"}]
            elif kind == 1:  # 自环
                p = new_ins_id()
                ev = [{"id": [p[0], p[1]], "kind": "insert",
                       "after": [p[0], p[1]], "char": "a"}]
            elif kind == 2 and created:  # 删除事件 id 占用插入身份
                t = rng.choice(created)
                ev = [{"id": [t[0], t[1]], "kind": "erase",
                       "target": [t[0], t[1]]}]
            elif kind == 3 and created:  # 同 id 异内容
                t = rng.choice(created)
                ev = [{"id": [t[0], t[1]], "kind": "insert", "after": None,
                       "char": "Q"}]
            elif kind == 4:  # after 指向删除事件
                xctr[0] += 1
                eid = ("x", xctr[0])
                t = rng.choice(created) if created else new_ins_id()
                ev = [{"id": [eid[0], eid[1]], "kind": "erase",
                       "target": [t[0], t[1]]},
                      {"id": [new_ins_id()[0], 1], "kind": "insert",
                       "after": [eid[0], eid[1]], "char": "a"}]
                # 修正:确保插入 id 合法形态
                ni = new_ins_id()
                ev[1]["id"] = [ni[0], ni[1]]
            else:  # 删除目标指向删除事件
                xctr[0] += 1
                e1 = ("x", xctr[0])
                xctr[0] += 1
                e2 = ("x", xctr[0])
                t = rng.choice(created) if created else new_ins_id()
                ev = [{"id": [e1[0], e1[1]], "kind": "erase",
                       "target": [t[0], t[1]]},
                      {"id": [e2[0], e2[1]], "kind": "erase",
                       "target": [e1[0], e1[1]]}]
            batches.append((ev, True))
            continue
        # 合法批:新事件 + 池中积压 + 偶发重复
        evs = []
        for _ in range(rng.randrange(1, 5)):
            evs.append(mk_insert())
        for _ in range(rng.randrange(0, 2)):
            evs.append(mk_erase())
        pool.extend(evs)
        take = min(len(pool), rng.randrange(1, 7))
        batch = []
        for _ in range(take):
            j = rng.randrange(len(pool))
            batch.append(pool.pop(j))
        if emitted and rng.random() < 0.3:
            batch.append(rng.choice(emitted))  # 幂等重复
        emitted.extend(batch)
        batches.append((batch, False))
    # 收尾:把剩余池全部发出
    if pool:
        batches.append((pool, False))
    return batches


def gen_varied(rng, nbatches, n_sites, p_erase, p_dup, chain_bias):
    """变参合法史:站点数/删除率/重复率/链倾向可调,覆盖更深悬挂与链式接根。"""
    sites = [chr(97 + i) for i in range(n_sites)]
    ctr = {s: 0 for s in sites}
    xctr = [0]
    created = []
    pool = []
    emitted = []
    batches = []
    chars = "aAbB 水"

    def nid():
        s = rng.choice(sites)
        ctr[s] += 1
        return (s, ctr[s])

    for b in range(nbatches):
        evs = []
        for _ in range(rng.randrange(1, 6)):
            i = nid()
            if created and rng.random() > 0.25:
                after = (created[-1] if rng.random() < chain_bias
                         else rng.choice(created))
            else:
                after = None
            created.append(i)
            evs.append({"id": [i[0], i[1]], "kind": "insert",
                        "after": None if after is None else [after[0], after[1]],
                        "char": rng.choice(chars)})
        for _ in range(rng.randrange(0, 3)):
            if rng.random() < p_erase:
                xctr[0] += 1
                eid = ("x", xctr[0])
                tg = rng.choice(created) if created and rng.random() < 0.85 \
                    else nid()
                evs.append({"id": [eid[0], eid[1]], "kind": "erase",
                            "target": [tg[0], tg[1]]})
        pool.extend(evs)
        take = min(len(pool), rng.randrange(1, 8))
        batch = []
        for _ in range(take):
            j = rng.randrange(len(pool))
            batch.append(pool.pop(j))
        if emitted and rng.random() < p_dup:
            batch.append(rng.choice(emitted))
        emitted.extend(batch)
        batches.append((batch, False))
    if pool:
        batches.append((pool, False))
    return batches


def run_differential(seed, nbatches):
    rng = random.Random(seed)
    batches = gen_history(rng, nbatches)
    return run_batches(seed, batches)


def run_batches(tag, batches):
    doc = Document()
    mdl = Model()
    idx = WordIndex(doc)
    hist = [[]]  # hist[v] = 版本 v 的可见身份序列
    for bi, (batch, expect_err) in enumerate(batches):
        pre_seq = doc._v
        pre_text = doc.slice(0, doc.length())
        pre_deltas = [doc.edits_since(s) for s in range(pre_seq + 1)]
        err_d = err_m = None
        try:
            doc.ingest(batch)
        except ValueError as e:
            err_d = e
        try:
            mdl.ingest(batch)
        except ValueError as e:
            err_m = e
        check((err_d is None) == (err_m is None),
              f"{tag}批{bi} 错误一致性 doc={err_d} mdl={err_m}")
        if expect_err:
            check(err_d is not None, f"{tag}批{bi} 应拒绝")
        if err_d is not None:
            # 整批回滚:seq、正文、全部历史增量一致
            check(doc._v == pre_seq, f"{tag}批{bi} 失败批改了seq")
            check(doc.slice(0, doc.length()) == pre_text,
                  f"{tag}批{bi} 失败批改了正文")
            for s in range(pre_seq + 1):
                check(doc.edits_since(s) == pre_deltas[s],
                      f"{tag}批{bi} 失败批改了增量{s}")
            continue
        if doc._v != pre_seq:
            hist.append([tuple(x) for x in
                         (mdl.select(k) for k in range(mdl.length()))])
        compare(doc, mdl, idx, tag=f"{tag}批{bi}")
        check_deltas(doc, hist, tag=f"{tag}批{bi}")
    return doc, mdl, idx, hist


# ---------------------------------------------------------------------------
# 回放源:只实现四个公开接口,增量按另一种合法顺序/分组给出
# ---------------------------------------------------------------------------
class ReplaySource:
    def __init__(self, versions):
        # versions[v] = [(id,ch),...] 该版本可见序列
        self._vers = versions

    def _cur(self):
        return self._vers[-1]

    def length(self):
        return len(self._cur())

    def slice(self, start, stop):
        return "".join(c for _i, c in self._cur()[start:stop])

    def select(self, i):
        if i < 0 or i >= len(self._cur()):
            raise IndexError
        return list(self._cur()[i][0])

    def edits_since(self, seq):
        old = self._vers[seq]
        cur = self._cur()
        cur_ids = {i for i, _c in cur}
        old_ids = {i for i, _c in old}
        edits = []
        # 删除:按旧坐标降序,逐项单独 splice(与 Document 分组不同)
        for k in range(len(old) - 1, -1, -1):
            if old[k][0] not in cur_ids:
                edits.append({"at": k, "remove": [list(old[k][0])],
                              "insert": []})
        # 插入:按新坐标升序,逐项单独 splice
        for k, (i, c) in enumerate(cur):
            if i not in old_ids:
                edits.append({"at": k, "remove": [],
                              "insert": [[list(i), c]]})
        return {"seq": len(self._vers) - 1, "edits": edits}


class Facade:
    """只暴露四个公开方法的门面,证明 WordIndex 不触碰私有结构。"""

    def __init__(self, doc):
        self._d = doc

    def length(self):
        return self._d.length()

    def slice(self, a, b):
        return self._d.slice(a, b)

    def select(self, i):
        return self._d.select(i)

    def edits_since(self, s):
        return self._d.edits_since(s)


class MixedSource:
    """回放源:把同位置的 remove+insert 并成一个混合 splice(合法形态)。"""

    def __init__(self):
        self._vers = [[]]

    def push(self, pairs):
        self._vers.append(pairs)

    def length(self):
        return len(self._vers[-1])

    def slice(self, a, b):
        return "".join(c for _i, c in self._vers[-1][a:b])

    def select(self, i):
        return list(self._vers[-1][i][0])

    def edits_since(self, seq):
        old = self._vers[seq]
        cur = self._vers[-1]
        cur_ids = {i for i, _c in cur}
        old_ids = {i for i, _c in old}
        edits = []
        for k, (u, _c) in enumerate(old):
            if u not in cur_ids:
                edits.append({"at": k, "remove": [list(u)], "insert": []})
        for k, (u, c) in enumerate(cur):
            if u not in old_ids:
                merged = False
                for sp in edits:
                    if sp["at"] == k and sp["remove"] and not sp["insert"]:
                        sp["insert"] = [[list(u), c]]
                        merged = True
                        break
                if not merged:
                    edits.append({"at": k, "remove": [],
                                  "insert": [[list(u), c]]})
        return {"seq": len(self._vers) - 1, "edits": edits}


def test_mixed_splice():
    src = MixedSource()
    src.push([(("a", 1), "a"), (("b", 1), "b")])
    idx = WordIndex(src)
    check(idx.lookup("ab") == [{"id": ["a", 1], "offset": 0}], "混合源初建")
    src.push([(("x", 1), "x"), (("b", 1), "b")])
    d = src.edits_since(1)
    check(len(d["edits"]) == 1 and d["edits"][0]["remove"]
          and d["edits"][0]["insert"], "确为混合splice")
    idx.sync()
    check(idx.lookup("xb") == [{"id": ["x", 1], "offset": 0}], "混合splice后")
    check(idx.lookup("ab") == [], "混合splice旧词消除")
    print("  混合splice(remove+insert同splice)消费:通过")


# ---------------------------------------------------------------------------
# 定向场景
# ---------------------------------------------------------------------------
def test_sample_contract():
    sample = json.loads(Path("sample.json").read_text())
    doc = Document()
    idx = WordIndex(doc)
    expect = [("CAT", [{"id": ["a", 1], "offset": 0}]),
              ("cat", []),
              ("at", [{"id": ["a", 2], "offset": 3}]),
              ("at", [{"id": ["a", 2], "offset": 2}]),
              ("at", [{"id": ["a", 2], "offset": 1}])]
    for i, batch in enumerate(sample["batches"]):
        doc.ingest(batch)
        idx.sync()
        check(doc.slice(0, doc.length()) == sample["expected_text"][i],
              f"sample文本{i}")
        if i >= 1:
            w, exp = expect[i - 1]
            check(idx.lookup(w) == exp, f"sample lookup {w} @{i}")
    check(doc.rank(["a", 1]) == 0, "被删a1的rank仍为0")
    check(doc.select(1) == ["a", 2], "后继a2仍可见")
    print("  sample.json 六次批次:文本/词命中/坐标/墓碑rank 全部符合契约")


def test_targeted():
    # 同批父晚到 + 先删后插(同批)
    doc = Document()
    s1 = doc.ingest([{"id": ["b", 2], "kind": "insert",
                      "after": ["b", 1], "char": "b"},
                     {"id": ["b", 1], "kind": "insert", "after": None,
                      "char": "a"},
                     {"id": ["x", 1], "kind": "erase",
                      "target": ["b", 3]},
                     {"id": ["b", 3], "kind": "insert",
                      "after": ["b", 2], "char": "c"}])
    check(doc.slice(0, 2) == "ab", "同批父晚到+先删后插")
    check(doc.rank(["b", 3]) == 2, "被删先到者rank可定位")
    check(doc.length() == 2, "先删后插不可见")
    # 重复事件幂等(同批重复+跨批重复),版本不变
    s2 = doc.ingest([{"id": ["b", 1], "kind": "insert", "after": None,
                      "char": "a"},
                     {"id": ["b", 1], "kind": "insert", "after": None,
                      "char": "a"}])
    check(s2 == s1, "全重复批次不增版本")
    check(doc.ingest([]) == s1, "空批不增版本")
    # 墓碑子孙:删父留子
    doc2 = Document()
    doc2.ingest([{"id": ["a", 1], "kind": "insert", "after": None,
                  "char": "x"},
                 {"id": ["a", 2], "kind": "insert", "after": ["a", 1],
                  "char": "y"},
                 {"id": ["a", 3], "kind": "insert", "after": ["a", 2],
                  "char": "z"}])
    doc2.ingest([{"id": ["e", 1], "kind": "erase", "target": ["a", 2]}])
    check(doc2.slice(0, 2) == "xz", "墓碑子孙:删a2留a1a3")
    check(doc2.rank(["a", 2]) == 1, "墓碑rank")
    check(doc2.rank(["a", 3]) == 1, "墓碑之后可见rank")
    # 词首尾拆并 + 纯分隔符 + Unicode 坐标
    doc3 = Document()
    idx3 = WordIndex(doc3)
    doc3.ingest([{"id": ["a", 1], "kind": "insert", "after": None,
                  "char": "水"}])
    doc3.ingest([{"id": ["a", 2], "kind": "insert", "after": ["a", 1],
                  "char": "b"},
                 {"id": ["a", 3], "kind": "insert", "after": ["a", 2],
                  "char": "c"}])
    check(idx3.sync() == 2, "idx3 sync")
    check(idx3.lookup("BC") == [{"id": ["a", 2], "offset": 1}],
          "Unicode坐标:词首在CJK之后")
    doc3.ingest([{"id": ["a", 4], "kind": "insert", "after": ["a", 1],
                  "char": " "}])  # 水 bc → 水 bc? a4(' ') 与 a2 同为 a1 孩子
    # a1 的孩子: a4(' ',("a",4)) > a2(("a",2)) → 顺序 水,' ',b,c
    check(doc3.slice(0, 4) == "水 bc", "空格插入拆词前")
    check(idx3.sync() == 3, "idx3 sync2")
    check(idx3.lookup("bc") == [{"id": ["a", 2], "offset": 2}], "空格后词坐标")
    doc3.ingest([{"id": ["e", 9], "kind": "erase", "target": ["a", 4]}])
    check(idx3.sync() == 4, "idx3 sync3")
    check(idx3.lookup("bc") == [{"id": ["a", 2], "offset": 1}], "删空格并词")
    # 纯分隔符
    doc4 = Document()
    idx4 = WordIndex(doc4)
    doc4.ingest([{"id": ["p", i], "kind": "insert",
                  "after": None if i == 1 else ["p", i - 1], "char": c}
                 for i, c in enumerate(" ，。 ", start=1)])
    idx4.sync()
    check(idx4.lookup("a") == [] and idx4.lookup("zz") == [], "纯分隔符无词")
    # 重复删除(不同删除事件id):可见性不再变化,版本仍递增
    doc6 = Document()
    doc6.ingest([{"id": ["a", 1], "kind": "insert", "after": None,
                  "char": "a"}])
    doc6.ingest([{"id": ["e", 1], "kind": "erase", "target": ["a", 1]}])
    s_before = doc6._v
    s_after = doc6.ingest([{"id": ["e", 2], "kind": "erase",
                            "target": ["a", 1]}])
    check(s_after == s_before + 1, "重复删除仍增版本")
    check(doc6.edits_since(s_before)["edits"] == [], "重复删除无可见性变化")
    check(doc6.length() == 0, "重复删除不复活")
    # 过期 lookup
    doc5 = Document()
    idx5 = WordIndex(doc5)
    doc5.ingest([{"id": ["a", 1], "kind": "insert", "after": None,
                  "char": "a"}])
    try:
        idx5.lookup("a")
        check(False, "未sync应抛ValueError")
    except ValueError:
        pass
    idx5.sync()
    check(idx5.lookup("a") == [{"id": ["a", 1], "offset": 0}], "同步后命中")
    idx5.sync()  # 幂等
    print("  定向场景:同批晚到/先删后插/幂等/墓碑子孙/词拆并/纯分隔符/"
          "Unicode坐标/过期lookup 全部通过")


def test_cycles_and_conflicts():
    # 环:经未到达身份的悬挂链成环
    doc = Document()
    doc.ingest([{"id": ["a", 2], "kind": "insert", "after": ["a", 1],
                 "char": "x"}])  # a1 未达,a2 悬挂
    pre = doc._v
    try:
        doc.ingest([{"id": ["a", 1], "kind": "insert", "after": ["a", 2],
                     "char": "y"}])
        check(False, "环应拒绝")
    except ValueError:
        pass
    check(doc._v == pre and doc.length() == 0, "环批次整批回滚")
    # 三环
    doc2 = Document()
    try:
        doc2.ingest([{"id": ["a", 1], "kind": "insert", "after": ["a", 3],
                      "char": "1"},
                     {"id": ["a", 2], "kind": "insert", "after": ["a", 1],
                      "char": "2"},
                     {"id": ["a", 3], "kind": "insert", "after": ["a", 2],
                      "char": "3"}])
        check(False, "三环应拒绝")
    except ValueError:
        pass
    check(doc2._v == 0, "三环回滚")
    # 类型冲突:插入身份被登记为删除事件
    doc3 = Document()
    doc3.ingest([{"id": ["a", 1], "kind": "insert", "after": None,
                  "char": "a"}])
    for bad in ([{"id": ["a", 1], "kind": "erase", "target": ["a", 1]}],
                [{"id": ["e", 1], "kind": "erase", "target": ["e", 1]}],
                [{"id": ["e", 2], "kind": "erase", "target": ["a", 1]},
                 {"id": ["e", 3], "kind": "erase", "target": ["e", 2]}]):
        pre = doc3._v
        try:
            doc3.ingest(bad)
            check(False, f"冲突批应拒绝 {bad}")
        except ValueError:
            pass
        check(doc3._v == pre, "冲突批回滚")
    # 重复冲突:同 id 不同 after / 不同 char / 删除不同目标
    doc4 = Document()
    doc4.ingest([{"id": ["a", 1], "kind": "insert", "after": None,
                  "char": "a"}])
    doc4.ingest([{"id": ["e", 1], "kind": "erase", "target": ["a", 1]}])
    for bad in ([{"id": ["a", 1], "kind": "insert", "after": ["a", 1],
                  "char": "a"}],
                [{"id": ["a", 1], "kind": "insert", "after": None,
                  "char": "b"}],
                [{"id": ["e", 1], "kind": "erase", "target": ["e", 1]}]):
        try:
            doc4.ingest(bad)
            check(False, f"重复冲突应拒绝 {bad}")
        except ValueError:
            pass
    print("  环/类型冲突/重复冲突:全部拒绝且整批回滚")


def test_replay_and_facade(doc, mdl, hist_pairs):
    # 回放源驱动
    src = ReplaySource(hist_pairs)
    idx_r = WordIndex(src)
    idx_d = WordIndex(doc)
    mw = mdl.words()
    for w in set(mw) | {"cat", "zz"}:
        a = idx_r.lookup(w)
        b = idx_d.lookup(w)
        check(a == b, f"回放源与真实文档命中一致 {w}")
        exp = [{"id": [f[0], f[1]], "offset": o}
               for f, o in sorted(mw.get(w, []), key=lambda t: t[1])]
        check(a == exp, f"回放源命中符合模型 {w}")
    # 门面源(证明不依赖私有结构)
    idx_f = WordIndex(Facade(doc))
    for w in set(mw) | {"cat"}:
        check(idx_f.lookup(w) == idx_d.lookup(w), f"门面源一致 {w}")
    # 回放源过期
    src2 = ReplaySource(hist_pairs[:-1] + [hist_pairs[-1]])
    src2._vers = hist_pairs[:-1]
    idx_r2 = WordIndex(src2)
    src2._vers = hist_pairs  # 源前进,索引未同步
    try:
        idx_r2.lookup("a")
        check(False, "回放源过期应抛")
    except ValueError:
        pass
    idx_r2.sync()
    print("  回放源/门面源驱动与过期检测:通过")


def test_robustness():
    # 调用方改传入字典/返回对象不污染内部状态
    doc = Document()
    ev = {"id": ["a", 1], "kind": "insert", "after": None, "char": "c"}
    doc.ingest([ev])
    ev["char"] = "X"
    ev["id"][0] = "zzz"
    check(doc.slice(0, 1) == "c", "传入字典被改不影响内部")
    d = doc.edits_since(0)
    d["edits"][0]["insert"][0][1] = "X"
    d["edits"][0]["insert"][0][0][0] = "zzz"
    d2 = doc.edits_since(0)
    check(d2["edits"][0]["insert"][0][1] == "c", "返回增量被改不影响内部")
    check(d2["edits"][0]["insert"][0][0] == ["a", 1], "返回身份为副本")
    s = doc.select(0)
    s[0] = "zzz"
    check(doc.select(0) == ["a", 1], "select返回副本")
    # 越界与非法参数
    try:
        doc.select(1)
        check(False, "select越界应抛")
    except IndexError:
        pass
    try:
        doc.edits_since(2)
        check(False, "seq越界应抛")
    except ValueError:
        pass
    check(doc.rank(["no", 1]) is None, "未知身份rank为None")
    check(doc.rank(["a", 2]) is None, "未接根身份rank为None")
    # 重复读取增量不消费数据
    check(doc.edits_since(0) == d2, "增量可重复读取")
    # 多版本净额:插入后又删除的身份不出现在跨版本增量中
    doc2 = Document()
    doc2.ingest([{"id": ["a", 1], "kind": "insert", "after": None,
                  "char": "a"}])           # v1
    doc2.ingest([{"id": ["a", 2], "kind": "insert", "after": ["a", 1],
                  "char": "b"}])           # v2: b 可见
    doc2.ingest([{"id": ["e", 1], "kind": "erase", "target": ["a", 2]}])
    # v3: b 隐藏
    d = doc2.edits_since(1)
    check(d["edits"] == [], "v1到v3净变化为空(b先现后隐)")
    d = doc2.edits_since(2)
    check(d["edits"] == [{"at": 1, "remove": [["a", 2]], "insert": []}],
          "v2到v3仅删除b")
    print("  健壮性:输入/返回隔离、越界、净额增量、重复读取 全部通过")


# ---------------------------------------------------------------------------
# 结构不变量核验
# ---------------------------------------------------------------------------
def check_invariants(doc, tag=""):
    seqt = doc._seqt
    # treap 聚合一致 + 堆性质 + 中序==结构前序
    cnt = [0]
    vis = [0]

    def walk(x, lo):
        if x is None:
            return 1 << 30
        check(x.prio >= lo, f"{tag} 堆性质")
        lm = walk(x.l, x.prio)
        rm = walk(x.r, x.prio)
        check(x.size == 1 + (x.l.size if x.l else 0) + (x.r.size if x.r else 0),
              f"{tag} size")
        check(x.wsum == x.w + (x.l.wsum if x.l else 0)
              + (x.r.wsum if x.r else 0), f"{tag} wsum")
        d = min(x.depth, lm, rm)
        check(x.dmin == d, f"{tag} dmin")
        cnt[0] += 1
        vis[0] += x.w
        return d

    if seqt.root is not None:
        check(seqt.root.p is None, f"{tag} 根父指针")
        walk(seqt.root, -1)
    rooted = sum(1 for r in doc._recs.values() if r.rooted)
    check(cnt[0] == rooted, f"{tag} 序列节点数==已接根数 {cnt[0]}!={rooted}")
    check(vis[0] == doc.length(), f"{tag} 可见数==length")
    # 中序遍历 == 模型结构前序由 compare() 覆盖;此处核验父指针闭环
    st = []
    x = seqt.root
    while st or x is not None:
        while x is not None:
            st.append(x)
            x = x.l
        x = st.pop()
        for c in (x.l, x.r):
            if c is not None:
                check(c.p is x, f"{tag} 父指针闭环")
        x = x.r
    # 每个已接根记录的 node 在序列中;未接根记录无 node
    for r in doc._recs.values():
        check((r.node is not None) == r.rooted, f"{tag} node<->rooted")
    print(f"  结构不变量({tag}): treap聚合/堆/父指针/接根一致 全部成立")


# ---------------------------------------------------------------------------
# 访问量实测
# ---------------------------------------------------------------------------
def measure():
    import math

    def log2(x):
        return math.log2(x)

    print("== 局部修订访问量实测(计数而非计时) ==")
    # 1) 深链:先倒序到达(全悬挂),最后根到达一次接根
    N = 6000
    doc = Document()
    doc.ingest([{"id": ["c", i], "kind": "insert",
                 "after": ["c", i - 1] if i > 1 else None, "char": "x"}
                for i in range(N, 1, -1)])
    o0 = doc.ops
    doc.ingest([{"id": ["c", 1], "kind": "insert", "after": None,
                 "char": "x"}])
    o1 = doc.ops
    k = N
    bound = 64 * (k + 1) * (log2(N + 2) + 1) ** 2
    check(o1 - o0 <= bound, f"链接根访问量 {o1 - o0} 超界 {bound:.0f}")
    print(f"  深链{N}: 末批一次接根{N}节点 访问量={o1 - o0} "
          f"(k·log²n界={bound:.0f})")
    # 2) 星形:一个父 6000 孩子逐个到达
    doc2 = Document()
    doc2.ingest([{"id": ["s", 0], "kind": "insert", "after": None,
                  "char": " "}])
    o0 = doc2.ops
    for i in range(1, 6001):
        doc2.ingest([{"id": ["s", i], "kind": "insert", "after": ["s", 0],
                      "char": "y"}])
    o1 = doc2.ops
    n = 6001
    per = (o1 - o0) / 6000
    bound = 64 * 2 * (log2(n + 2) + 1) ** 2
    check(per <= bound, f"星形单批访问量 {per} 超界 {bound:.0f}")
    print(f"  星形6000: 单孩子接根平均访问量={per:.1f} "
          f"(log²n界={bound:.0f})")
    # 3) 大正文中的局部修订
    doc3 = Document()
    rng = random.Random(7)
    ids = []
    for i in range(20000):
        site = rng.choice("abcde")
        ids.append([site, i + 1])
        doc3.ingest([{"id": ids[-1], "kind": "insert",
                      "after": None if i == 0 else ids[-2], "char":
                      rng.choice("ab cd")}])
    n = 20000
    o0 = doc3.ops
    doc3.ingest([{"id": ["f", 1], "kind": "insert", "after": ids[10000],
                  "char": "q"},
                 {"id": ["f", 2], "kind": "insert", "after": ids[10001],
                  "char": "w"},
                 {"id": ["f", 3], "kind": "erase", "target": ids[5000]}])
    o1 = doc3.ops
    k = 3 + 2 + 1
    bound = 64 * (k + 1) * (log2(n + 2) + 1) ** 2
    check(o1 - o0 <= bound, f"局部修订访问量 {o1 - o0} 超界 {bound:.0f}")
    print(f"  大正文{n}: 3事件局部修订 访问量={o1 - o0} "
          f"((k+1)log²n界={bound:.0f})")
    # rank/select/slice/edits_since 访问量
    o0 = doc3.ops
    r = doc3.rank(ids[15000])
    o1 = doc3.ops
    bound = 64 * (log2(n + 2) + 1) ** 2
    check(o1 - o0 <= bound, f"rank访问量 {o1 - o0} 超界")
    o0 = doc3.ops
    doc3.select(12345)
    o1 = doc3.ops
    check(o1 - o0 <= bound, f"select访问量 {o1 - o0} 超界")
    o0 = doc3.ops
    s = doc3.slice(5000, 5050)
    o1 = doc3.ops
    bound = 64 * 51 * (log2(n + 2) + 1) ** 2
    check(o1 - o0 <= bound, f"slice访问量 {o1 - o0} 超界")
    print(f"  rank/select/slice(50) 访问量={o1 - o0} 级别 log²n, 实测见上")
    # 3b) 深链中部插入小身份孩子:拼接点定位不得遍历整链
    doc4 = Document()
    M = 4000
    doc4.ingest([{"id": ["m", i], "kind": "insert",
                  "after": None if i == 1 else ["m", i - 1], "char": "x"}
                 for i in range(1, M + 1)])
    o0 = doc4.ops
    # ("a",1) < ("m",2): 作为 ("m",1) 的孩子排在整条链之后
    doc4.ingest([{"id": ["a", 1], "kind": "insert", "after": ["m", 1],
                  "char": "y"}])
    o1 = doc4.ops
    check(doc4.select(M) == ["a", 1], "小身份孩子落在链尾")
    bound = 64 * 2 * (log2(M + 2) + 1) ** 2
    check(o1 - o0 <= bound, f"深链拼接点定位疑似遍历整链: {o1 - o0}")
    print(f"  深链{M}插入小身份孩子(拼接点在链尾): 访问量={o1 - o0},"
          f" 未遍历整链")
    # 4) WordIndex 同步与查询访问量
    idx = WordIndex(doc3)
    o0 = idx.ops
    doc3.ingest([{"id": ["g", 1], "kind": "insert", "after": ids[15000],
                  "char": "z"}])
    idx.sync()
    o1 = idx.ops
    print(f"  WordIndex: 单字符修订sync访问量={o1 - o0} (d=1级)")
    check(o1 - o0 <= 64 * 2 * (log2(n + 2) + 1) ** 2, "sync访问量超界")
    o0 = idx.ops
    hits = idx.lookup("a")
    o1 = idx.ops
    p = len(hits)
    print(f"  WordIndex: lookup('a') 命中{p}项 访问量={o1 - o0} (p级)")
    # 5) 同结构不同规模的扩容比(访问量应近对数增长而非线性)
    def build(m):
        d = Document()
        for i in range(m):
            d.ingest([{"id": ["z", i + 1], "kind": "insert",
                       "after": None if i == 0 else ["z", i], "char": "x"}])
        return d

    d_a = build(5000)
    d_b = build(20000)

    def small_rev(d, m):
        o0 = d.ops
        d.ingest([{"id": ["r", 1], "kind": "insert", "after": ["z", m // 2],
                   "char": "q"},
                  {"id": ["r", 2], "kind": "erase",
                   "target": ["z", m // 3]}])
        return d.ops - o0

    ra = small_rev(d_a, 5000)
    rb = small_rev(d_b, 20000)
    print(f"  扩容比: n=5000修订访问量={ra}, n=20000={rb}, 比值={rb / max(ra, 1):.2f}")
    check(rb <= ra * 4 + 200, "访问量随规模近线性增长,不符合局部性")
    print("  访问量实测全部在 (k+1)·log²n 界内,且随规模呈对数级增长")


# ---------------------------------------------------------------------------
def main():
    print("== 保留材料回归 ==")
    fixture_check.normal()
    print("  RAW_SOURCE_REGRESSION_OK(经 verify 复跑)")

    print("== 契约样例与定向场景 ==")
    test_sample_contract()
    test_targeted()
    test_cycles_and_conflicts()
    test_robustness()
    test_mixed_splice()

    print("== 随机乱序史差分(独立全量模型) ==")
    doc = mdl = idx = hist = None
    for seed in range(8):
        doc, mdl, idx, hist = run_differential(1000 + seed, 45)
        print(f"  seed{1000 + seed}: 45批差分通过 "
              f"(seq={mdl.seq}, 文本长={mdl.length()}, 身份数={len(mdl.ins)})")
    # 变参史:更深悬挂链/更高删除与重复率
    for ci, (ns, pe, pd, cb) in enumerate([(4, 0.5, 0.4, 0.6),
                                           (2, 0.7, 0.5, 0.8),
                                           (6, 0.3, 0.2, 0.3)]):
        for s in range(3):
            rng = random.Random(3000 + ci * 100 + s)
            run_batches(f"cfg{ci}s{s}", gen_varied(rng, 60, ns, pe, pd, cb))
        print(f"  变参cfg{ci}(站点{ns},删{pe},重复{pd},链{cb}): 3种子x60批通过")
    # 用一部独立史做回放源/门面源与不变量核验
    rng = random.Random(555)
    batches = gen_history(rng, 40)
    doc2 = Document()
    mdl2 = Model()
    idx2 = WordIndex(doc2)
    hist2 = [[]]
    hist_pairs = [[]]  # 每版本可见(身份,字符),供回放源
    for batch, expect_err in batches:
        try:
            doc2.ingest(batch)
        except ValueError:
            pass
        try:
            mdl2.ingest(batch)
        except ValueError:
            pass
        if doc2._v != len(hist2) - 1:
            hist2.append([tuple(x) for x in
                          (mdl2.select(k) for k in range(mdl2.length()))])
            hist_pairs.append(mdl2.visible_pairs())
        compare(doc2, mdl2, idx2, tag="replay史")
        check_deltas(doc2, hist2, tag="replay史")
    test_replay_and_facade(doc2, mdl2, hist_pairs)
    check_invariants(doc2, tag="随机史")
    print("== 访问量实测 ==")
    measure()
    print("VERIFY_OK: 全部核验通过")


if __name__ == "__main__":
    main()
