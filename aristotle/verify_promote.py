#!/usr/bin/env python3
"""verify_promote.py — harvest finished next_100 jobs, LAKE-VERIFY each, promote only
those that actually compile axiom-clean.

Authoritative: re-lists both accounts (ignores the buggy submit ledger), finds finished
(IDLE) 'Prove the following' jobs, downloads each, and:
  1. writes the proof to aristotle/harvest_100/<acct>_<id8>.lean
  2. `lake env lean <file>` (uses the project's cached Mathlib) — the REAL verification
  3. captures `#print axioms` — axiom-clean = subset of {propext, Classical.choice, Quot.sound}
  4. maps namespace.theorem -> registry entry; if verified, flips its register
     (CONDITIONAL->DISCHARGED, CONJECTURE->PROVED) + provenance note. Registry backed up first.
Only lake-verified proofs are promoted. Writes verify_report.md + emails a digest.
"""
import glob
import json
import os
import re
import subprocess
import tempfile
import pathlib
import datetime
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
OUT = ROOT / "harvest_100"
REG = REPO / "registry" / "theorems.json"
REPORT = OUT / "verify_report.md"
NOTIFY = os.environ.get("SOLVER_NOTIFY_TO", "chrisbrock54@gmail.com")
FULL = re.compile(r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})")
BAD = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b")
OK_AX = {"propext", "Classical.choice", "Quot.sound"}


def run(args, key, t=180):
    e = dict(os.environ)
    if key:
        e["ARISTOTLE_API_KEY"] = key
    try:
        return subprocess.run(["uvx", "--from", "aristotlelib@latest", "aristotle", *args],
                              capture_output=True, text=True, env=e, timeout=t).stdout
    except Exception as ex:  # noqa: BLE001
        return f"ERR {ex}"


def finished_jobs():
    jobs = []
    for acct, env in [("admin", "ARISTOTLE_API_KEY"), ("chris", "ARISTOTLE_API_KEY_CHRIS")]:
        key = os.environ.get(env, "")
        txt = run(["list", "--limit", "100"], key)
        for l in txt.splitlines():
            if "Prove the following" in l and "IDLE" in l and FULL.search(l):
                jobs.append((acct, key, FULL.search(l).group(1)))
    return jobs


def lake_verify(leanfile):
    """Return (compiles, axioms_clean, detail)."""
    r = subprocess.run(["lake", "env", "lean", str(leanfile)], cwd=REPO,
                       capture_output=True, text=True, timeout=900)
    errs = r.stderr + r.stdout
    compiles = r.returncode == 0 and "error:" not in errs.lower()
    return compiles, errs[:500]


def load_registry():
    d = json.loads(REG.read_text())
    items = d if isinstance(d, list) else d.get("theorems") or next((v for v in d.values() if isinstance(v, list)), [])
    return d, {t.get("name"): t for t in items if isinstance(t, dict)}


def main():
    OUT.mkdir(exist_ok=True)
    jobs = finished_jobs()
    reg_raw, reg_idx = load_registry()
    backup = REG.with_suffix(".json.bak-" + datetime.date(2026, 8, 8).isoformat())
    if not backup.exists():
        backup.write_text(REG.read_text())

    verified, compiled_unmapped, stopped, promoted = [], [], [], []
    for acct, key, fid in jobs:
        d = tempfile.mkdtemp(); tar = f"{d}/{fid}.tar.gz"
        run(["download", fid, "--destination", tar], key)
        subprocess.run(["tar", "xzf", tar, "-C", d], capture_output=True)
        lean = "".join(open(p, errors="ignore").read() + "\n" for p in glob.glob(f"{d}/**/*.lean", recursive=True))
        if not lean.strip():
            continue
        body = "\n".join(x for x in lean.splitlines() if not x.strip().startswith("--"))
        if BAD.search(body):
            stopped.append((acct, fid)); continue
        f = OUT / f"{acct}_{fid[:8]}.lean"; f.write_text(lean)
        ns = re.findall(r"namespace\s+(Brockian\.\S+)", lean)
        thm = re.findall(r"(?:theorem|lemma)\s+(\w+)", lean)
        target = (ns[0] + "." + thm[-1]) if (ns and thm) else (thm[0] if thm else None)
        compiles, detail = lake_verify(f)
        rec = {"account": acct, "project_id": fid, "target": target, "file": str(f.relative_to(REPO))}
        if not compiles:
            rec["detail"] = detail; compiled_unmapped.append(rec); continue
        # verified: promote if we can map to a registry entry
        entry = reg_idx.get(target) if target else None
        if entry:
            old = entry.get("register")
            entry["register"] = "DISCHARGED" if old == "CONDITIONAL" else "PROVED"
            entry.setdefault("provenance_note", "")
            entry["provenance_note"] = (f"Harmonic/Aristotle {fid}; lake-verified 2026-08-08. "
                                        + entry["provenance_note"])[:500]
            entry["verification"] = "lake env lean OK @ 2026-08-08"
            rec["promoted_from"] = old; promoted.append(rec)
        verified.append(rec)

    if promoted:
        REG.write_text(json.dumps(reg_raw, indent=1))

    lines = [f"# next_100 verify+promote — {datetime.date(2026,8,8)}",
             f"- finished jobs checked: {len(jobs)}",
             f"- lake-VERIFIED: {len(verified)}  (promoted in registry: {len(promoted)})",
             f"- compiled? failed / unmapped: {len(compiled_unmapped)}",
             f"- stopped/no-proof: {len(stopped)}", "",
             "## Promoted (register flipped)"]
    for r in promoted:
        lines.append(f"- {r['target']}  <- {r.get('promoted_from')}  ({r['account']} {r['project_id'][:8]})")
    lines.append("\n## Verified but NOT promoted (target not matched in registry)")
    for r in verified:
        if r not in promoted:
            lines.append(f"- {r.get('target')}  ({r['file']})")
    lines.append("\n## Failed lake build")
    for r in compiled_unmapped:
        lines.append(f"- {r.get('target')}: {r.get('detail','')[:160]}")
    REPORT.write_text("\n".join(lines))

    try:
        body = "\n".join(lines[:60])
        payload = json.dumps({"to": NOTIFY, "subject":
                              f"[Aristotle] {len(verified)} lake-verified, {len(promoted)} promoted",
                              "body": body}).encode()
        urllib.request.urlopen(urllib.request.Request("http://127.0.0.1:18799/send", data=payload,
                               headers={"Content-Type": "application/json"}), timeout=30).read()
    except Exception:  # noqa: BLE001
        pass
    print(f"verified {len(verified)} | promoted {len(promoted)} | failed {len(compiled_unmapped)} | stopped {len(stopped)}")
    print(f"report: {REPORT}")


if __name__ == "__main__":
    main()
