"""quotedoc — 乱序送达正文修订的合并(Document)与独立词索引投影(WordIndex)。

仅用 Python 标准库实现。

结构不变量(实现赖以正确、verify.py 实测断言的性质):
1. 每个插入身份对应结构树中一个节点;父引用 after 指向另一插入身份或 null 根。
   同一父的直接孩子按身份 (site,counter) 降序,以前序遍历确定唯一结构序;
   字符可见时先输出自身再输出孩子。被删插入只把自身权重置 0(墓碑),
   结构位置与后继不消失;已接根节点永不脱根,已删字符永不复活。
2. 已接根节点全部进入一棵按结构序的随机 treap(含墓碑),节点维护:
   size(子树节点数)、wsum(子树可见权重和)、dmin(子树最小结构深度)。
   结构深度自接根起不变,因此"某节点子树末尾"= 序列中其后首个 depth<=自身
   的位置,可用 dmin 在 O(log n) 期望时间定位,无需遍历子树。
3. 未到父的整支后代留在各父的孩子索引中,不进序列;当最高缺失祖先到达时,
   整支按前序遍历一次性拼接,拼接点由"父的已接根孩子中身份小于新支的最大者"
   或"父子树末尾"定位。新接根节点数计入当批 k。
4. 可见性变迁(新可见/新隐藏)按版本记入 vlog;edits_since 据 vlog 与当前
   treap 的 rank 计算净 splice 增量,不输出未变化字符,不重建全文。
5. 引用环用可回滚并查集(按秩合并、不压缩路径)在 O(log n) 内判定;
   批校验全部通过才提交,失败批不接纳任何事件、改动或版本。
"""
from bisect import bisect_left as _bisect_left
import random as _random

_RNG = _random.Random(0x51EED00C)

__all__ = ["Document", "WordIndex"]


# ---------------------------------------------------------------------------
# 序列 treap:按结构序,维护 size / wsum(可见权重) / dmin(最小深度)
# ---------------------------------------------------------------------------
class _SNode:
    __slots__ = ("ref", "ch", "w", "depth", "prio", "l", "r", "p",
                 "size", "wsum", "dmin")

    def __init__(self, ref, ch, w, depth):
        self.ref = ref          # Document: 插入记录;WordIndex: 身份元组
        self.ch = ch            # 该节点的单个 Unicode 字符
        self.w = w              # 可见权重 1 / 墓碑 0
        self.depth = depth      # 结构深度(接根后不变)
        self.prio = _RNG.getrandbits(30)
        self.l = self.r = self.p = None
        self.size = 1
        self.wsum = w
        self.dmin = depth


def _sz(x):
    return x.size if x is not None else 0


def _ws(x):
    return x.wsum if x is not None else 0


class _Seq:
    """结构序 treap;ops 计数器记录内部节点访问量(供复杂度实测)。"""

    __slots__ = ("root", "_ops")

    def __init__(self, ops):
        self.root = None
        self._ops = ops

    def _upd(self, x):
        self._ops[0] += 1
        l = x.l
        r = x.r
        x.size = 1 + _sz(l) + _sz(r)
        x.wsum = x.w + _ws(l) + _ws(r)
        d = x.depth
        if l is not None and l.dmin < d:
            d = l.dmin
        if r is not None and r.dmin < d:
            d = r.dmin
        x.dmin = d

    def _merge(self, a, b):
        if a is None:
            if b is not None:
                b.p = None
            return b
        if b is None:
            a.p = None
            return a
        if a.prio < b.prio:
            s = self._merge(a.r, b)
            a.r = s
            if s is not None:
                s.p = a
            a.p = None
            self._upd(a)
            return a
        s = self._merge(a, b.l)
        b.l = s
        if s is not None:
            s.p = b
        b.p = None
        self._upd(b)
        return b

    def _split(self, x, k):
        # 前 k 个节点(按结构序)进左树
        if x is None:
            return (None, None)
        if _sz(x.l) >= k:
            l, r = self._split(x.l, k)
            x.l = r
            if r is not None:
                r.p = x
            x.p = None
            self._upd(x)
            if l is not None:
                l.p = None
            return (l, x)
        l, r = self._split(x.r, k - _sz(x.l) - 1)
        x.r = l
        if l is not None:
            l.p = x
        x.p = None
        self._upd(x)
        if r is not None:
            r.p = None
        return (x, r)

    def insert_at(self, k, node):
        node.l = node.r = node.p = None
        self._upd(node)
        l, r = self._split(self.root, k)
        self.root = self._merge(self._merge(l, node), r)

    def delete_node(self, x):
        sub = self._merge(x.l, x.r)
        p = x.p
        x.l = x.r = x.p = None
        if p is None:
            self.root = sub
            return
        if p.l is x:
            p.l = sub
        else:
            p.r = sub
        if sub is not None:
            sub.p = p
        y = p
        while y is not None:
            self._upd(y)
            y = y.p

    def size(self):
        return _sz(self.root)

    def visible(self):
        return _ws(self.root)

    def index_of(self, x):
        # 节点在结构序中的下标(含墓碑)
        i = _sz(x.l)
        self._ops[0] += 1
        while x.p is not None:
            self._ops[0] += 1
            if x.p.r is x:
                i += _sz(x.p.l) + 1
            x = x.p
        return i

    def vrank_of(self, x):
        # 节点之前(结构序)的可见字符数
        i = _ws(x.l)
        self._ops[0] += 1
        while x.p is not None:
            self._ops[0] += 1
            if x.p.r is x:
                i += _ws(x.p.l) + x.p.w
            x = x.p
        return i

    def select_v(self, k):
        # 第 k 个可见节点(0 起)
        x = self.root
        while x is not None:
            self._ops[0] += 1
            lw = _ws(x.l)
            if k < lw:
                x = x.l
            elif k < lw + x.w:
                return x
            else:
                k -= lw + x.w
                x = x.r
        return None

    def select_i(self, i):
        # 结构序第 i 个节点(含墓碑)
        x = self.root
        while x is not None:
            self._ops[0] += 1
            ls = _sz(x.l)
            if i < ls:
                x = x.l
            elif i == ls:
                return x
            else:
                i -= ls + 1
                x = x.r
        return None

    def char_at(self, i):
        n = self.select_i(i)
        return n.ch if n is not None else None

    def collect(self, lo, hi):
        # 可见 rank 落在 [lo,hi) 的节点,按结构序;零可见子树整棵剪枝
        out = []
        self._collect(self.root, 0, lo, hi, out)
        return out

    def _collect(self, x, base, lo, hi, out):
        if x is None:
            return
        ws = x.wsum
        if ws == 0 or base + ws <= lo or base >= hi:
            return
        self._ops[0] += 1
        lw = _ws(x.l)
        self._collect(x.l, base, lo, hi, out)
        here = base + lw
        if x.w and lo <= here < hi:
            out.append(x)
        self._collect(x.r, here + x.w, lo, hi, out)

    def first_shallow_after(self, pos, d):
        # 结构序中 pos 之后首个 depth<=d 的下标;无则 None
        return self._fsa(self.root, 0, pos, d)

    def _fsa(self, x, base, pos, d):
        if x is None:
            return None
        if base + x.size - 1 <= pos:
            return None
        if x.dmin > d:
            return None
        self._ops[0] += 1
        ls = _sz(x.l)
        r = self._fsa(x.l, base, pos, d)
        if r is not None:
            return r
        if base + ls > pos and x.depth <= d:
            return base + ls
        return self._fsa(x.r, base + ls + 1, pos, d)

    def set_weight(self, x, w):
        if x.w == w:
            return
        x.w = w
        y = x
        while y is not None:
            self._upd(y)
            y = y.p


# ---------------------------------------------------------------------------
# 键序 treap:孩子索引(按身份排序),支持前驱与遍历
# ---------------------------------------------------------------------------
class _KNode:
    __slots__ = ("key", "rec", "prio", "l", "r")

    def __init__(self, key, rec):
        self.key = key
        self.rec = rec
        self.prio = _RNG.getrandbits(30)
        self.l = self.r = None


class _KTree:
    __slots__ = ("root", "_ops")

    def __init__(self, ops):
        self.root = None
        self._ops = ops

    def insert(self, key, rec):
        self.root = self._ins(self.root, key, rec)

    def _ins(self, x, key, rec):
        self._ops[0] += 1
        if x is None:
            return _KNode(key, rec)
        if key < x.key:
            x.l = self._ins(x.l, key, rec)
            if x.l.prio < x.prio:
                y = x.l
                x.l = y.r
                y.r = x
                return y
            return x
        x.r = self._ins(x.r, key, rec)
        if x.r.prio < x.prio:
            y = x.r
            x.r = y.l
            y.l = x
            return y
        return x

    def predecessor(self, key):
        # 严格小于 key 的最大键
        x = self.root
        best = None
        while x is not None:
            self._ops[0] += 1
            if x.key < key:
                best = x
                x = x.r
            else:
                x = x.l
        return best.rec if best is not None else None

    def items(self):
        # 升序遍历 (key, rec)
        st = []
        x = self.root
        while st or x is not None:
            while x is not None:
                self._ops[0] += 1
                st.append(x)
                x = x.l
            x = st.pop()
            yield (x.key, x.rec)
            x = x.r


# ---------------------------------------------------------------------------
# Document
# ---------------------------------------------------------------------------
class _Rec:
    __slots__ = ("id", "ch", "after", "erased", "arrived", "rooted",
                 "node", "depth", "vv", "vh", "kids", "rkids")

    def __init__(self, idt):
        self.id = idt           # (site, counter)
        self.ch = None
        self.after = None       # 父身份或 None
        self.erased = False     # 删除标记(可先于插入到达)
        self.arrived = False    # 插入事件是否已到达
        self.rooted = False     # 是否已接根(接根后永不脱根)
        self.node = None        # 序列 treap 节点(接根时创建)
        self.depth = 0          # 结构深度(接根时确定)
        self.vv = None          # 首次可见的版本
        self.vh = None          # 转为隐藏的版本
        self.kids = None        # _KTree: 已到达直接孩子
        self.rkids = None       # _KTree: 已接根直接孩子


class Document:
    """多采集端乱序修订合并出的唯一正文。"""

    def __init__(self):
        self._ops = [0]
        self._recs = {}          # 插入型身份(已到达或被引用保留) -> _Rec
        self._erases = {}        # 删除事件身份 -> 目标身份
        self._uf_p = {}          # 可回滚并查集(仅插入型身份参与)
        self._uf_r = {}
        self._seqt = _Seq(self._ops)
        self._top_kids = _KTree(self._ops)
        self._top_rkids = _KTree(self._ops)
        self._vlog = []          # (版本, 身份, +1可见/-1隐藏)
        self._v = 0

    @property
    def ops(self):
        """内部访问量计数(供复杂度实测,非接口契约)。"""
        return self._ops[0]

    # ---------------- 并查集(可回滚) ----------------
    def _uf_add(self, x):
        if x not in self._uf_p:
            self._uf_p[x] = x
            self._uf_r[x] = 0

    def _uf_find(self, x):
        p = self._uf_p
        r = x
        while p[r] != r:
            self._ops[0] += 1
            r = p[r]
        return r

    def _uf_union(self, a, b, done):
        ra = self._uf_find(a)
        rb = self._uf_find(b)
        if self._uf_r[ra] < self._uf_r[rb]:
            ra, rb = rb, ra
        done.append((rb, ra, self._uf_r[ra]))
        self._uf_p[rb] = ra
        if self._uf_r[ra] == self._uf_r[rb]:
            self._uf_r[ra] += 1

    def _uf_undo(self, done):
        for rb, ra, oldrank in reversed(done):
            self._uf_p[rb] = rb
            self._uf_r[ra] = oldrank

    # ---------------- 孩子索引 ----------------
    def _kids_of(self, prec):
        if prec is None:
            return self._top_kids
        if prec.kids is None:
            prec.kids = _KTree(self._ops)
        return prec.kids

    def _rkids_of(self, prec):
        if prec is None:
            return self._top_rkids
        if prec.rkids is None:
            prec.rkids = _KTree(self._ops)
        return prec.rkids

    # ---------------- 合并 ----------------
    def ingest(self, events):
        # 1) 规范化+批内去重(同 id 同内容幂等,异内容冲突)
        norm = []
        seen = {}
        for e in events:
            idl = e["id"]
            idt = (idl[0], idl[1])
            if e["kind"] == "insert":
                af = e["after"]
                ne = ("i", idt, None if af is None else (af[0], af[1]),
                      e["char"])
            else:
                tg = e["target"]
                ne = ("e", idt, (tg[0], tg[1]))
            prev = seen.get(idt)
            if prev is None:
                seen[idt] = ne
                norm.append(ne)
            elif prev != ne:
                raise ValueError("同id异内容")
        if not norm:
            return self._v
        # 2) 类型与引用核验(不改动已提交状态)
        batch_er = set()
        for ne in norm:
            if ne[0] == "e":
                batch_er.add(ne[1])
        new_ins = []
        new_ers = []
        for ne in norm:
            if ne[0] == "i":
                _, idt, after, ch = ne
                if idt in self._erases or idt in batch_er:
                    raise ValueError("插入身份与删除事件冲突")
                rec = self._recs.get(idt)
                if rec is not None and rec.arrived:
                    if rec.after == after and rec.ch == ch:
                        continue  # 幂等重复
                    raise ValueError("同id异内容")
                if after is not None and (after in self._erases
                                          or after in batch_er):
                    raise ValueError("父引用指向删除事件")
                new_ins.append(ne)
            else:
                _, eid, tg = ne
                if eid in self._recs:
                    raise ValueError("删除事件身份与插入身份冲突")
                prev = self._erases.get(eid)
                if prev is not None:
                    if prev == tg:
                        continue  # 幂等重复
                    raise ValueError("同id异内容")
                if tg in self._erases or tg in batch_er:
                    raise ValueError("删除引用指向删除事件")
                new_ers.append(ne)
        if not new_ins and not new_ers:
            return self._v
        # 3) 环核验(可回滚并查集;已有图无环,组件皆为树)
        done = []
        try:
            for ne in new_ins:
                _, idt, after, _ch = ne
                if after is None:
                    continue
                self._uf_add(idt)
                self._uf_add(after)
                if self._uf_find(idt) == self._uf_find(after):
                    raise ValueError("引用成环")
                self._uf_union(idt, after, done)
        except ValueError:
            self._uf_undo(done)
            raise
        # 4) 提交
        newv = self._v + 1
        newset = set()
        newrecs = []
        for ne in new_ins:
            _, idt, after, ch = ne
            rec = self._recs.get(idt)
            if rec is None:
                rec = _Rec(idt)
                self._recs[idt] = rec
            rec.arrived = True
            rec.after = after
            rec.ch = ch
            newset.add(rec)
            newrecs.append(rec)
            prec = None
            if after is not None:
                prec = self._recs.get(after)
                if prec is None:
                    prec = _Rec(after)
                    self._recs[after] = prec
            self._kids_of(prec).insert(idt, rec)
        for ne in new_ers:
            _, eid, tg = ne
            self._erases[eid] = tg
            trec = self._recs.get(tg)
            if trec is None:
                trec = _Rec(tg)
                self._recs[tg] = trec
            trec.erased = True
        # 4b) 接根:仅当 after 链在本批内全部到达并通向根。
        # 顶支 = 可接根且其父不会在本批接根的新插入(父已接根或为根)。
        # 必须先依据接根前状态定全部顶支,再统一拼接,否则旧悬挂后代
        # 会被祖先分支与本支重复拼接。
        memo = {}
        tops = []
        for rec in newrecs:
            if not self._rootable(rec, newset, memo):
                continue
            if rec.after is not None:
                prec = self._recs[rec.after]
                if (not prec.rooted) and self._rootable(prec, newset, memo):
                    continue  # 父将在本批接根,rec 由其分支覆盖
                tops.append(rec)
            else:
                tops.append(rec)
        for rec in tops:
            prec = self._recs[rec.after] if rec.after is not None else None
            self._splice(rec, prec, newv)
        # 4c) 隐藏:本批删除命中的已接根可见节点
        for ne in new_ers:
            trec = self._recs[ne[2]]
            nd = trec.node
            if (trec.arrived and trec.rooted and nd is not None
                    and nd.w == 1):
                self._seqt.set_weight(nd, 0)
                trec.vh = newv
                self._vlog.append((newv, trec.id, -1))
        self._v = newv
        return newv

    def _rootable(self, rec, newset, memo):
        # 本批新插入 rec 的 after 链是否通向根(沿链共享末端答案)
        st = []
        r = rec
        while True:
            res = memo.get(r)
            if res is not None:
                break
            if r.after is None:
                res = True
                break
            arec = self._recs[r.after]
            if not arec.arrived:
                res = False
                break
            if arec not in newset:
                res = arec.rooted
                break
            st.append(r)
            r = arec
        memo[r] = res
        for u in st:
            memo[u] = res
        return res

    def _splice(self, xrec, prec, newv):
        # 把 xrec 的整支已到达后代按前序遍历接入序列(迭代,不用递归)
        seqt = self._seqt
        rk = self._rkids_of(prec) if prec is not None else self._top_rkids
        t = rk.predecessor(xrec.id) if rk is not None else None
        if t is not None:
            pos = seqt.index_of(t.node)
        elif prec is None:
            pos = seqt.size()
        else:
            pos = seqt.first_shallow_after(seqt.index_of(prec.node),
                                           prec.depth)
            if pos is None:
                pos = seqt.size()
        d0 = 0 if prec is None else prec.depth + 1
        j = 0
        st = [(xrec, prec, d0)]
        while st:
            u, uprec, d = st.pop()
            u.rooted = True
            u.depth = d
            w = 0 if u.erased else 1
            nd = _SNode(u, u.ch, w, d)
            u.node = nd
            seqt.insert_at(pos + j, nd)
            j += 1
            self._rkids_of(uprec).insert(u.id, u)
            if w:
                u.vv = newv
                self._vlog.append((newv, u.id, 1))
            ks = u.kids
            if ks is not None:
                for _cid, crec in ks.items():
                    st.append((crec, u, d + 1))

    # ---------------- 查询 ----------------
    def length(self):
        return self._seqt.visible()

    def slice(self, start, stop):
        n = self.length()
        if not (0 <= start <= stop <= n):
            raise ValueError("slice坐标越界")
        return "".join(x.ch for x in self._seqt.collect(start, stop))

    def rank(self, id):
        rec = self._recs.get((id[0], id[1]))
        if rec is None or not rec.rooted:
            return None
        return self._seqt.vrank_of(rec.node)

    def select(self, i):
        if not isinstance(i, int) or i < 0 or i >= self.length():
            raise IndexError("select越界")
        nd = self._seqt.select_v(i)
        rid = nd.ref.id
        return [rid[0], rid[1]]

    # ---------------- 公开增量 ----------------
    def edits_since(self, seq):
        if not isinstance(seq, int) or not (0 <= seq <= self._v):
            raise ValueError("seq越界")
        cur = self._v
        seqt = self._seqt
        # 净变化集合:R=seq时可见而今隐藏;I=seq后新可见且仍可见
        i0 = _bisect_left(self._vlog, (seq + 1,))
        irecs = []
        rrecs = []
        for j in range(i0, len(self._vlog)):
            v, idc, sign = self._vlog[j]
            rec = self._recs[idc]
            if sign > 0:
                if rec.vh is None:
                    irecs.append(rec)
            else:
                if rec.vv <= seq:
                    rrecs.append(rec)
        # 结构位置与当前可见 rank
        ipos = sorted((seqt.index_of(r.node), seqt.vrank_of(r.node), r)
                      for r in irecs)
        rpos = sorted((seqt.index_of(r.node), seqt.vrank_of(r.node), r)
                      for r in rrecs)
        ipositions = [p for p, _vr, _r in ipos]
        edits = []
        # 删除:按旧可见 rank 降序执行,连续段并为一个 splice
        rlist = []
        for k, (p, vr, r) in enumerate(rpos):
            before_i = _bisect_left(ipositions, p)
            rlist.append((vr + k - before_i, r))
        rlist.sort(key=lambda t: -t[0])
        g = []
        for rk0, r in rlist:
            if g and rk0 != g[-1][0] - 1:
                edits.append(self._mk_remove(g))
                g = []
            g.append((rk0, r))
        if g:
            edits.append(self._mk_remove(g))
        # 插入:按当前可见 rank 升序执行,连续段并为一个 splice
        g = []
        for _p, vr, r in ipos:
            if g and vr != g[-1][0] + 1:
                edits.append(self._mk_insert(g))
                g = []
            g.append((vr, r))
        if g:
            edits.append(self._mk_insert(g))
        return {"seq": cur, "edits": edits}

    @staticmethod
    def _mk_remove(g):
        g = list(reversed(g))  # 升序
        return {"at": g[0][0],
                "remove": [[r.id[0], r.id[1]] for _rk, r in g],
                "insert": []}

    @staticmethod
    def _mk_insert(g):
        return {"at": g[0][0],
                "remove": [],
                "insert": [[[r.id[0], r.id[1]], r.ch] for _vr, r in g]}


# ---------------------------------------------------------------------------
# WordIndex:仅经公开接口 length/slice/select/edits_since 驱动的词投影
# ---------------------------------------------------------------------------
def _is_letter(c):
    return ("A" <= c <= "Z") or ("a" <= c <= "z")


def _scan_words(nodes):
    # 一串顺序节点 -> [(小写词, 首字符身份)]
    out = []
    i = 0
    n = len(nodes)
    while i < n:
        c = nodes[i].ch
        if _is_letter(c):
            j = i + 1
            chars = [c]
            while j < n and _is_letter(nodes[j].ch):
                chars.append(nodes[j].ch)
                j += 1
            out.append(("".join(chars).lower(), nodes[i].ref))
            i = j
        else:
            i += 1
    return out


class WordIndex:
    """大小写不敏感的完整 ASCII 词索引;只消费公开编辑增量。"""

    def __init__(self, document):
        self._doc = document
        self._ops = [0]
        self._seqt = _Seq(self._ops)   # 可见身份序列镜像
        self._byid = {}                # 身份 -> 序列节点
        self._words = {}               # 小写词 -> {首字符身份}
        self._seq = 0
        self.sync()

    @property
    def ops(self):
        return self._ops[0]

    def sync(self):
        d = self._doc.edits_since(self._seq)
        for sp in d["edits"]:
            self._apply(sp)
        self._seq = d["seq"]
        return self._seq

    def _apply(self, sp):
        at = sp["at"]
        rem = sp["remove"]
        ins = sp["insert"]
        rl = len(rem)
        il = len(ins)
        if rl == 0 and il == 0:
            return
        seqt = self._seqt
        # 校验 remove 身份逐项匹配
        rnodes = []
        for i, idl in enumerate(rem):
            key = (idl[0], idl[1])
            nd = self._byid.get(key)
            if nd is None or seqt.index_of(nd) != at + i:
                raise ValueError("增量与索引序列不一致")
            rnodes.append((key, nd))
        m = seqt.size()
        # 旧受影响词区间 [L,R):向两侧扩展到完整词边界
        L = at
        if L > 0 and _is_letter(seqt.char_at(L - 1)):
            L -= 1
            while L > 0 and _is_letter(seqt.char_at(L - 1)):
                L -= 1
        R = at + rl
        if R < m and _is_letter(seqt.char_at(R)):
            R += 1
            while R < m and _is_letter(seqt.char_at(R)):
                R += 1
        # 摘除旧词命中
        if R > L:
            for w, fid in _scan_words(seqt.collect(L, R)):
                s = self._words.get(w)
                if s is not None:
                    s.discard(fid)
                    if not s:
                        del self._words[w]
                self._ops[0] += 1
        # 应用序列变更
        for key, nd in rnodes:
            seqt.delete_node(nd)
            del self._byid[key]
        for j, (idl, ch) in enumerate(ins):
            key = (idl[0], idl[1])
            nd = _SNode(key, ch, 1, 0)
            seqt.insert_at(at + j, nd)
            self._byid[key] = nd
        # 登记新词命中
        R2 = R - rl + il
        if R2 > L:
            for w, fid in _scan_words(seqt.collect(L, R2)):
                self._words.setdefault(w, set()).add(fid)
                self._ops[0] += 1

    def lookup(self, word):
        # 只允许读取 seq,不得据此完成 sync
        d = self._doc.edits_since(self._seq)
        if d["seq"] != self._seq:
            raise ValueError("索引未同步")
        if (not isinstance(word, str) or not (1 <= len(word) <= 64)
                or not word.isascii() or not word.isalpha()):
            return []
        hits = self._words.get(word.lower())
        if not hits:
            return []
        seqt = self._seqt
        byid = self._byid
        out = []
        for key in hits:
            out.append({"id": [key[0], key[1]],
                        "offset": seqt.index_of(byid[key])})
        out.sort(key=lambda h: (h["offset"], h["id"]))
        return out
