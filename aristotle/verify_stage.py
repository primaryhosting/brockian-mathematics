#!/usr/bin/env python3
"""verify_stage.py — robustly lake-verify the harvested proofs and STAGE promotions
(does NOT edit registry/theorems.json — it's already dirty from in-flight work).

- Operates on the already-downloaded aristotle/harvest_100/*.lean (no re-download).
- Per file: `lake env lean <file>` with a per-file timeout, isolated (one timeout
  never kills the run), resumable via verify_state.json.
- Maps namespace.theorem -> registry entry; records a PROPOSED promotion
  (CONDITIONAL->DISCHARGED / CONJECTURE->PROVED) into proposed_promotions.json.
- Parallelism: 2 workers (lean+Mathlib is memory-heavy on 16GB).
Apply step (separate, on user OK): apply_promotions.py reads proposed_promotions.json.
"""
import concurrent.futures as cf
import glob
import json
import os
import re
import subprocess
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
OUT = ROOT / "harvest_100"
REG = REPO / "registry" / "theorems.json"
STATE = OUT / "verify_state.json"
PROPOSED = OUT / "proposed_promotions.json"
REPORT = OUT / "verify_report.md"
TIMEOUT = int(os.environ.get("VERIFY_TIMEOUT", "1500"))
WORKERS = int(os.environ.get("VERIFY_WORKERS", "2"))


def reg_index():
    d = json.loads(REG.read_text())
    items = d if isinstance(d, list) else d.get("theorems") or next((v for v in d.values() if isinstance(v, list)), [])
    return {t["name"]: t for t in items if isinstance(t, dict) and "name" in t}


def targets_in(lean, idx):
    """All registry entries whose fullname (namespace.theorem) appears in this file."""
    nss = re.findall(r"namespace\s+(Brockian\.\S+|Brockian)", lean)
    thms = re.findall(r"(?:theorem|lemma)\s+(\w+)", lean)
    hits = []
    for name, entry in idx.items():
        short = name.split(".")[-1]
        if short in thms and any(name.startswith(ns) or name.rsplit(".", 1)[0].endswith(ns.split(".")[-1]) for ns in nss):
            hits.append((name, entry.get("register")))
    return hits


def verify_one(f):
    try:
        r = subprocess.run(["lake", "env", "lean", f], cwd=REPO,
                           capture_output=True, text=True, timeout=TIMEOUT)
        errs = (r.stderr + r.stdout)
        ok = r.returncode == 0 and "error:" not in errs.lower()
        return f, ok, ("" if ok else errs[:300])
    except subprocess.TimeoutExpired:
        return f, None, f"timeout >{TIMEOUT}s"
    except Exception as e:  # noqa: BLE001
        return f, None, str(e)[:200]


def main():
    idx = reg_index()
    state = json.loads(STATE.read_text()) if STATE.exists() else {}
    files = sorted(glob.glob(str(OUT / "*.lean")))
    todo = [f for f in files if os.path.basename(f) not in state]
    print(f"{len(files)} proofs, {len(todo)} to verify ({WORKERS} workers, {TIMEOUT}s cap each)")

    with cf.ThreadPoolExecutor(max_workers=WORKERS) as ex:
        for f, ok, detail in ex.map(verify_one, todo):
            b = os.path.basename(f)
            lean = open(f, errors="ignore").read()
            hits = targets_in(lean, idx)
            state[b] = {"compiles": ok, "detail": detail,
                        "targets": [{"name": n, "register": r} for n, r in hits]}
            STATE.write_text(json.dumps(state, indent=1))
            print(f"  {'OK ' if ok else 'xx '} {b}  targets={[n.split('.')[-1] for n,_ in hits] or '?'}  {detail[:60]}")

    # stage proposed promotions from verified files
    proposed = {}
    for b, s in state.items():
        if not s.get("compiles"):
            continue
        for t in s["targets"]:
            new = "DISCHARGED" if t["register"] == "CONDITIONAL" else ("PROVED" if t["register"] == "CONJECTURE" else None)
            if new:
                proposed[t["name"]] = {"from": t["register"], "to": new, "proof_file": b}
    PROPOSED.write_text(json.dumps(proposed, indent=1))

    verified = [b for b, s in state.items() if s.get("compiles")]
    failed = [b for b, s in state.items() if s.get("compiles") is False]
    pend = [b for b, s in state.items() if s.get("compiles") is None]
    lines = [f"# verify+stage — {len(verified)}/{len(state)} compiled",
             f"- lake-VERIFIED: {len(verified)}",
             f"- failed: {len(failed)} | timed-out/pending: {len(pend)}",
             f"- PROPOSED promotions (staged, not applied): {len(proposed)}", "",
             "## Proposed promotions"]
    for name, p in sorted(proposed.items()):
        lines.append(f"- {name}: {p['from']} -> {p['to']}  ({p['proof_file']})")
    lines.append("\n## Verified files w/o a registry match (new lemmas / helper-only)")
    for b, s in state.items():
        if s.get("compiles") and not s["targets"]:
            lines.append(f"- {b}")
    lines.append("\n## Failed / timed out")
    for b, s in state.items():
        if not s.get("compiles"):
            lines.append(f"- {b}: {s.get('detail','')[:120]}")
    REPORT.write_text("\n".join(lines))
    print(f"\nverified {len(verified)} | proposed {len(proposed)} | failed {len(failed)} | pending {len(pend)}")
    print(f"report {REPORT}\nproposed {PROPOSED}")


if __name__ == "__main__":
    main()
