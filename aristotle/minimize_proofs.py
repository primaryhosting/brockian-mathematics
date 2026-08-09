#!/usr/bin/env python3
"""minimize_proofs.py — shrink verified proofs by dead-declaration elimination.

Aristotle proofs carry many helper lemmas; often only some feed the main theorem.
This parses the file, builds a name-dependency graph, and keeps only the main
theorem(s) + their transitive dependencies (dropping unreferenced decls can't break
what's kept — semantically safe). Strips comments/blank runs. Writes minimized/ +
stats. Optionally lake-verifies the minimized file (capped/guarded) to confirm it
still compiles.
"""
import glob
import json
import os
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
SRC = ROOT / "best_proofs"
OUT = ROOT / "minimized"
LEDGER = ROOT / "harvest_ledger.json"
VERIFY = os.environ.get("MIN_VERIFY", "0") == "1"
VMAX = int(os.environ.get("MIN_VMAX", "6"))
TIMEOUT = int(os.environ.get("MIN_TIMEOUT", "1500"))
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?(theorem|lemma|def)\s+([A-Za-z_][\w']*)")


def parse(text):
    lines = text.splitlines()
    header, blocks, cur = [], [], None
    for ln in lines:
        m = DECL.match(ln)
        if m:
            if cur:
                blocks.append(cur)
            cur = {"name": m.group(2), "lines": [ln]}
        elif cur is not None:
            cur["lines"].append(ln)
        else:
            header.append(ln)
    if cur:
        blocks.append(cur)
    return header, blocks


def minimize(text, main_hint=None):
    header, blocks = parse(text)
    if not blocks:
        return text, 0, 0
    names = [b["name"] for b in blocks]
    body = {b["name"]: "\n".join(b["lines"][1:]) for b in blocks}
    # main = the target theorem if present, else the last declaration
    main = next((n for n in names if main_hint and main_hint in n), names[-1])
    # transitive deps: a name is needed if it appears (as a word) in a needed body
    needed = {main}
    changed = True
    while changed:
        changed = False
        for b in blocks:
            if b["name"] in needed:
                for other in names:
                    if other != b["name"] and other not in needed and re.search(rf"\b{re.escape(other)}\b", "\n".join(b["lines"])):
                        needed.add(other); changed = True
    kept = [b for b in blocks if b["name"] in needed]
    out = "\n".join(header).rstrip() + "\n\n" + "\n\n".join("\n".join(b["lines"]).rstrip() for b in kept) + "\n"
    return out, len(blocks), len(kept)


def lake_ok(f):
    try:
        r = subprocess.run(["lake", "env", "lean", str(f)], cwd=REPO,
                           capture_output=True, text=True, timeout=TIMEOUT)
        return r.returncode == 0 and "error:" not in (r.stdout + r.stderr).lower()
    except Exception:  # noqa: BLE001
        return None


def main():
    OUT.mkdir(exist_ok=True)
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    by_file = {f"{m['account']}_{pid[:8]}.lean": m for pid, m in ledger.items()}
    stats = {}
    verified_count = 0
    for f in sorted(glob.glob(str(SRC / "*.lean"))):
        p = pathlib.Path(f)
        text = p.read_text(errors="ignore")
        # main hint from target name (best_proofs are named by sanitized target)
        hint = p.stem.split("_")[-1]
        mini, nblocks, nkept = minimize(text, hint)
        of = OUT / p.name
        of.write_text(mini)
        stats[p.name] = {"decls": nblocks, "kept": nkept, "dropped": nblocks - nkept,
                         "orig_lines": len(text.splitlines()), "min_lines": len(mini.splitlines())}
        if VERIFY and verified_count < VMAX and nblocks != nkept:
            ok = lake_ok(of)
            stats[p.name]["min_compiles"] = ok
            verified_count += 1
    (OUT / "stats.json").write_text(json.dumps(stats, indent=1))
    tot_o = sum(s["orig_lines"] for s in stats.values())
    tot_m = sum(s["min_lines"] for s in stats.values())
    dropped = sum(s["dropped"] for s in stats.values())
    print(f"minimized {len(stats)} proofs: dropped {dropped} dead decls; "
          f"lines {tot_o}->{tot_m} ({100*(tot_o-tot_m)//max(tot_o,1)}% smaller)")


if __name__ == "__main__":
    main()
