#!/usr/bin/env python3
"""lemma_mine.py — salvage value from FAILED attempts. A stopped job (its headline
goal left as sorry) usually still contains many fully-proved helper lemmas. Mine the
complete (sorry-free) declarations out of every harvested proof file — especially the
STOPPED ones — into mined_lemmas/, so nothing Aristotle actually proved is wasted.

Heuristic Lean splitter (no build): header (imports/open/namespace) + per-declaration
blocks; a block is kept iff its body has no sorry/admit/native_decide/sorryAx.
"""
import glob
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent
H = ROOT / "harvest_100"
LEDGER = ROOT / "harvest_ledger.json"
OUT = ROOT / "mined_lemmas"
BAD = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b")
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?(theorem|lemma|def)\s+([A-Za-z_][\w']*)")


def split_decls(text):
    lines = text.splitlines()
    header, blocks, cur, started = [], [], [], False
    for ln in lines:
        if DECL.match(ln):
            if cur:
                blocks.append(cur)
            cur = [ln]; started = True
        elif started:
            cur.append(ln)
        else:
            header.append(ln)
    if cur:
        blocks.append(cur)
    return "\n".join(header), blocks


def main():
    OUT.mkdir(exist_ok=True)
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    by_file = {f"{m['account']}_{pid[:8]}.lean": m for pid, m in ledger.items()}
    mined = {}
    total = 0
    for f in glob.glob(str(H / "*.lean")):
        name = pathlib.Path(f).name
        meta = by_file.get(name, {})
        text = open(f, errors="ignore").read()
        header, blocks = split_decls(text)
        keep = []
        for b in blocks:
            block = "\n".join(b)
            body = "\n".join(l for l in b if not l.strip().startswith("--"))
            if not BAD.search(body):
                m = DECL.match(b[0])
                keep.append((m.group(2), block))
        if not keep:
            continue
        target = meta.get("target", name)
        safe = re.sub(r"[^A-Za-z0-9]+", "_", target)
        d = OUT / safe; d.mkdir(exist_ok=True)
        for lemname, block in keep:
            (d / f"{lemname}.lean").write_text(header + "\n\n" + block + "\n")
        mined[target] = {"source": name, "verdict": meta.get("verdict"),
                         "lemmas": [k for k, _ in keep]}
        total += len(keep)
    (OUT / "manifest.json").write_text(json.dumps(mined, indent=1))
    salvaged = sum(1 for m in mined.values() if m["verdict"] == "STOPPED")
    print(f"mined {total} complete lemmas from {len(mined)} files "
          f"({salvaged} of them from STOPPED/failed jobs — salvaged value)")


if __name__ == "__main__":
    main()
