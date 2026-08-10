#!/usr/bin/env python3
"""annotate_headers.py — make AXLE-verified best_proofs human-legible + PR-ready.

For every best_proofs/<target>.lean that AXLE verified, rewrite it to:
  1. NORMALIZED form (imports hoisted+deduped to the top) — this is exactly the text
     AXLE kernel-checked, so the shipped file is the verified file (fixes the prior
     gap where auto_pr shipped raw Aristotle output with a mid-file duplicate import).
  2. A leading `/-! ... -/` doc header naming the problem (category, human name,
     statement) — a comment is inert to the kernel, so verification still holds.

Idempotent (skips files already headed). Statements pulled from all queue files.
"""
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import titles  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent
BEST = ROOT / "best_proofs"
OUT = ROOT / "pr_ready"   # shippable copies: normalized (verified form) + human header
AXLE = ROOT / "axle_verify.json"
HARV = ROOT / "harvest_ledger.json"
QUEUE_FILES = ["domains_queue.json", "mined_queue.json", "next_100.json",
               "pca_lean_queue.json", "frontier_queue.json", "frontier2.json",
               "reattack_queue.json", "frontier_spectral.json"]


def normalize(content: str) -> str:
    imports, body = [], []
    for l in content.splitlines():
        if l.strip().startswith("import "):
            if l.strip() not in imports:
                imports.append(l.strip())
        else:
            body.append(l)
    # drop any pre-existing leading doc header so this is idempotent
    text = "\n".join(body)
    text = re.sub(r"\A\s*/-!.*?-/\s*", "", text, count=1, flags=re.S)
    return "\n".join(imports), text.lstrip("\n")


def main():
    axle = json.loads(AXLE.read_text()) if AXLE.exists() else {}
    har = json.loads(HARV.read_text()) if HARV.exists() else {}
    tier_of = {}
    for pid, m in har.items():
        if m.get("verdict") == "PROVED":
            tier_of.setdefault(m["target"], m.get("tier"))
    stmt = {}
    for qf in QUEUE_FILES:
        p = ROOT / qf
        if p.exists():
            d = json.loads(p.read_text())
            q = d["queue"] if isinstance(d, dict) else d
            for it in q:
                stmt.setdefault(it["target"], it.get("statement"))

    def san(t):
        return re.sub(r"[^A-Za-z0-9]+", "_", t) + ".lean"

    OUT.mkdir(exist_ok=True)
    verified = {t for t in tier_of if axle.get(san(t), {}).get("verified") is True}
    done = 0
    for target in sorted(verified):
        f = BEST / san(target)
        if not f.exists():
            continue
        imports, body = normalize(f.read_text(errors="ignore"))
        head = titles.header(target, tier_of.get(target), stmt.get(target), verified=True)
        (OUT / san(target)).write_text(head + "\n\n" + imports + "\n\n" + body + "\n")
        done += 1
    print(f"annotated + normalized {done} AXLE-verified proofs -> {OUT}/")


if __name__ == "__main__":
    main()
