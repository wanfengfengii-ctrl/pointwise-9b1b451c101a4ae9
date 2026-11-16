"""demo.py — 现场演示:晚到字符、空格与删除如何同步改变词命中与坐标。

所有输出均来自对 quotedoc.Document / WordIndex 的真实调用,无预置答案。
"""
import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
os.chdir(Path(__file__).resolve().parent)

from wire import read
from quotedoc import Document, WordIndex


def show(doc, idx, words, note):
    idx.sync()
    text = doc.slice(0, doc.length())
    print(f"    {note:<30} 正文={text!r}")
    for w in words:
        hits = [(h["id"], h["offset"]) for h in idx.lookup(w)]
        print(f"        lookup({w!r}) -> {hits}")


def main():
    print("一、sample.json 原始事件经 wire.read 逐字节还原后逐批合并")
    print("   (父片段晚到 → 空格插入 → 删除旧锚点,词与坐标实时变化)")
    sample = json.loads(Path("sample.json").read_text())
    doc = Document()
    idx = WordIndex(doc)
    prev = 0
    for bi, batch in enumerate(sample["batches"]):
        wire = "\n".join(json.dumps(e, ensure_ascii=False)
                         for e in batch).encode()
        events = list(read([wire[i:i + 1] for i in range(len(wire))]))
        seq = doc.ingest(events)
        delta = doc.edits_since(prev)
        print(f"  批次{bi + 1}: seq={seq} 公开增量={delta['edits']}")
        show(doc, idx, ["cat", "at", "crat"], f"批次{bi + 1}后")
        prev = seq
    print(f"    被删 ['a',1] 的 rank={doc.rank(['a', 1])}"
          f"(仍可定位), select(1)={doc.select(1)}(后继仍可见)")

    print()
    print("二、晚到父片段让整词凭空出现,空格拆词、删除并词")
    doc = Document()
    idx = WordIndex(doc)
    # "ello"+"world" 先到但父缺失;"h" 晚到后整支接根
    batch1 = ([{"id": ["h", i], "kind": "insert",
                "after": ["h", i - 1], "char": c}
               for i, c in enumerate("ello", start=1)] +
              [{"id": ["w", i + 1], "kind": "insert",
                "after": ["h", 4] if i == 0 else ["w", i], "char": c}
               for i, c in enumerate("world")])
    doc.ingest(batch1)
    show(doc, idx, ["hello", "world", "helloworld"],
         "ello/world先到但父缺失")
    doc.ingest([{"id": ["h", 0], "kind": "insert", "after": None,
                 "char": "h"}])
    show(doc, idx, ["hello", "world", "helloworld"], "晚到'h'接根后")
    # 空格插入拆词(身份大于 w1,故排在 hello 与 world 之间)
    doc.ingest([{"id": ["z", 1], "kind": "insert", "after": ["h", 4],
                 "char": " "}])
    show(doc, idx, ["hello", "world", "helloworld"], "插入空格拆词后")
    # 删除空格并词
    doc.ingest([{"id": ["x", 1], "kind": "erase", "target": ["z", 1]}])
    show(doc, idx, ["hello", "world", "helloworld"], "删除空格并词后")
    # 词首再删:'h'被删,词首身份与坐标同步变化
    doc.ingest([{"id": ["x", 2], "kind": "erase", "target": ["h", 0]}])
    show(doc, idx, ["helloworld", "elloworld"], "删除词首'h'后")
    print(f"    被删 ['h',0] 的 rank={doc.rank(['h', 0])},"
          f" select(0)={doc.select(0)}")

    print()
    print("三、大小写不敏感与 Unicode 分隔(坐标按字符计)")
    doc = Document()
    idx = WordIndex(doc)
    doc.ingest([{"id": ["u", 1], "kind": "insert", "after": None,
                 "char": "水"},
                {"id": ["u", 2], "kind": "insert", "after": ["u", 1],
                 "char": "C"},
                {"id": ["u", 3], "kind": "insert", "after": ["u", 2],
                 "char": "a"},
                {"id": ["u", 4], "kind": "insert", "after": ["u", 3],
                 "char": "T"}])
    show(doc, idx, ["cat", "CAT", "cAt"], "CJK分隔+大写词")
    print()
    print("DEMO_OK: 以上词命中与坐标均由实时调用产生")


if __name__ == "__main__":
    main()
