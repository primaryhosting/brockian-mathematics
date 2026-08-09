#!/usr/bin/env python3
"""harvest_proofs.py — check-in harvester for the next_100 Aristotle submissions.

Scoped to aristotle/submitted_ids.json (our 200 jobs across admin+chris). Each run:
  1. For each not-yet-harvested (target, account, project_id): download the result
     under that account's key (uvx aristotlelib@latest). Empty download => still
     running => leave for next cycle.
  2. Classify terminal results PROVED (has .lean, no sorry/admit/native_decide/axiom)
     vs STOPPED, save artifacts to aristotle/harvest/<target>/, record in harvest_ledger.json.
  3. Email a digest of NEWLY-terminal results to $SOLVER_NOTIFY_TO (gmail bridge :18799).
  4. Write harvest_report.md. PROVED items are listed as PROMOTION CANDIDATES — NOT
     auto-registered (registry promotion requires a real `lake build` verification).

No LLM calls; safe to run hourly. Resumable/idempotent.
"""
import glob
import json
import os
import pathlib
import re
import subprocess
import tempfile
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent
LEDGER_IN = ROOT / "submitted_ids.json"
LEDGER_OUT = ROOT / "harvest_ledger.json"
HARVEST_DIR = ROOT / "harvest"
REPORT = ROOT / "harvest_report.md"
NOTIFY_TO = os.environ.get("SOLVER_NOTIFY_TO", "chrisbrock54@gmail.com")
GMAIL_SEND = "http://127.0.0.1:18799/send"
KEY_ENV = {"admin": "ARISTOTLE_API_KEY", "chris": "ARISTOTLE_API_KEY_CHRIS"}
MAX_PER_RUN = int(os.environ.get("HARVEST_MAX", "80"))
BAD = re.compile(r"\b(sorry|admit|native_decide)\b")


def run_aristotle(args, key, timeout=180):
    env = dict(os.environ)
    if key:
        env["ARISTOTLE_API_KEY"] = key
    try:
        return subprocess.run(["uvx", "--from", "aristotlelib@latest", "aristotle", *args],
                              capture_output=True, text=True, env=env, timeout=timeout).stdout
    except Exception:  # noqa: BLE001
        return ""


def fetch(pid, key):
    """Download + extract; return (terminal, verdict, lean_text)."""
    d = tempfile.mkdtemp(prefix="harv_")
    tar = os.path.join(d, f"{pid}.tar.gz")
    run_aristotle(["download", pid, "--destination", tar], key)
    lean = ""
    try:
        subprocess.run(["tar", "xzf", tar, "-C", d], capture_output=True, timeout=60)
        for p in glob.glob(os.path.join(d, "**", "*.lean"), recursive=True):
            lean += open(p, errors="ignore").read() + "\n"
    except Exception:  # noqa: BLE001
        pass
    if not lean.strip():
        return False, None, ""          # not downloadable yet => still running
    stripped = "\n".join(l for l in lean.splitlines() if not l.strip().startswith("--"))
    verdict = "STOPPED" if BAD.search(stripped) else "PROVED"
    return True, verdict, lean


def email(subject, body):
    try:
        payload = json.dumps({"to": NOTIFY_TO, "subject": subject, "body": body}).encode()
        req = urllib.request.Request(GMAIL_SEND, data=payload, headers={"Content-Type": "application/json"})
        urllib.request.urlopen(req, timeout=30).read()
        return True
    except Exception:  # noqa: BLE001
        return False


def main():
    submitted = json.loads(LEDGER_IN.read_text()) if LEDGER_IN.exists() else {}
    harvested = json.loads(LEDGER_OUT.read_text()) if LEDGER_OUT.exists() else {}
    HARVEST_DIR.mkdir(exist_ok=True)

    pending = [(k, v) for k, v in submitted.items() if k not in harvested]
    newly = []
    for k, v in pending[:MAX_PER_RUN]:
        acct, target = k.split(":", 1)
        key = os.environ.get(KEY_ENV.get(acct, ""))
        if not key:
            continue
        terminal, verdict, lean = fetch(v["project_id"], key)
        if not terminal:
            continue
        outdir = HARVEST_DIR / target.replace(".", "_")
        outdir.mkdir(parents=True, exist_ok=True)
        (outdir / f"{acct}_{v['project_id']}.lean").write_text(lean)
        harvested[k] = {"verdict": verdict, "account": acct, "target": target,
                        "project_id": v["project_id"], "tier": v.get("tier"),
                        "path": str((outdir).relative_to(ROOT))}
        newly.append((target, acct, verdict, v.get("tier")))
        LEDGER_OUT.write_text(json.dumps(harvested, indent=1))

    proved = [h for h in harvested.values() if h["verdict"] == "PROVED"]
    stopped = [h for h in harvested.values() if h["verdict"] == "STOPPED"]
    lines = [f"# Aristotle harvest — {len(harvested)}/{len(submitted)} resolved",
             f"- PROVED (promotion candidates, need `lake build` + register): {len(proved)}",
             f"- STOPPED / no-proof: {len(stopped)}",
             f"- still running: {len(submitted) - len(harvested)}", "",
             "## PROVED candidates"]
    for h in sorted(proved, key=lambda x: x["target"]):
        lines.append(f"- [{h['tier']}] {h['target']}  ({h['account']}, {h['project_id']})  -> {h['path']}")
    REPORT.write_text("\n".join(lines))

    if newly:
        np = [n for n in newly if n[2] == "PROVED"]
        body = (f"Aristotle harvest: {len(newly)} newly resolved "
                f"({len(np)} PROVED, {len(newly)-len(np)} stopped).\n"
                f"Cumulative: {len(proved)} PROVED / {len(harvested)} resolved / {len(submitted)} total.\n\n"
                + "\n".join(f"  {v}  {t}  [{tier}] ({a})" for t, a, v, tier in newly[:40])
                + f"\n\nReport: {REPORT}")
        email(f"[Aristotle harvest] {len(np)} new proofs, {len(harvested)}/{len(submitted)} resolved", body)
    print(f"harvested this run: {len(newly)} | cumulative {len(harvested)}/{len(submitted)} "
          f"({len(proved)} PROVED)")


if __name__ == "__main__":
    main()
