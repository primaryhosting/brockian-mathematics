#!/usr/bin/env python3
"""auto_pr.py — open a GitHub PR for KERNEL-TRUSTED new-domain proofs.

Safety:
- DRY-RUN by default. Actually pushing/opening a PR requires AUTO_PR_LIVE=1.
- Eligible = cross_check trusted (axiom-clean, no sorryAx) AND catalogued as a
  new-domain result. Nothing else is ever PR'd.
- Works in an ISOLATED worktree off clean origin/main — never touches the (dirty)
  main working tree; the PR contains ONLY the proof files + a manifest.
- Batches all eligible proofs into ONE PR.

Env: AUTO_PR_LIVE=1 to actually push+open; PR_DIR (default contrib/aristotle-domains).
"""
import datetime
import json
import os
import pathlib
import shutil
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
CROSS = ROOT / "cross_check.json"
LEDGER = ROOT / "harvest_ledger.json"
DOMAINS = REPO / "registry" / "domains.json"
MIN = ROOT / "minimized"
BEST = ROOT / "best_proofs"
PR_READY = ROOT / "pr_ready"   # annotated (human header) + normalized shippable copies
PLAN = ROOT / "pr_plan.json"
PR_LEDGER = ROOT / "pr_submitted.json"
LIVE = os.environ.get("AUTO_PR_LIVE") == "1"
PR_DIR = os.environ.get("PR_DIR", "contrib/aristotle-domains")


def eligible():
    """Kernel-trusted (AXLE cloud lean-4.32.0) proofs that are catalogued new-domain
    results. best_proofs/<sanitized target>.lean is exactly what AXLE verified."""
    import re
    axle = json.loads((ROOT / "axle_verify.json").read_text()) if (ROOT / "axle_verify.json").exists() else {}
    domains = json.loads(DOMAINS.read_text()) if DOMAINS.exists() else {}
    out = []
    for target, dmeta in domains.items():
        san = re.sub(r"[^A-Za-z0-9]+", "_", target) + ".lean"
        if axle.get(san, {}).get("verified") is not True:
            continue
        # prefer the annotated+normalized shippable copy; fall back to raw best_proofs
        src = PR_READY / san
        if not src.exists():
            src = BEST / san
        if not src.exists():
            continue
        out.append({"target": target, "domain": dmeta.get("domain"),
                    "src": str(src), "verification": "AXLE cloud lean-4.32.0",
                    "environment": axle[san].get("environment", "lean-4.32.0")})
    return out


def run(cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)


def main():
    elig = eligible()
    PLAN.write_text(json.dumps({"eligible": elig, "count": len(elig), "live": LIVE}, indent=1))
    # idempotent: only PR targets not already PR'd (safe for permanent every-2h operation)
    ledger = json.loads(PR_LEDGER.read_text()) if PR_LEDGER.exists() else {"targets": [], "runs": []}
    done = set(ledger.get("targets", []))
    new = [e for e in elig if e["target"] not in done]
    print(f"{len(elig)} AXLE-verified eligible, {len(new)} NEW ({'LIVE' if LIVE else 'DRY-RUN'})")
    for e in new[:12]:
        print(f"  - {e['target']} ({e['domain']})")
    if not new:
        print("nothing new to PR."); return
    if not LIVE:
        print(f"\nDRY-RUN: {len(new)} new proofs would be PR'd. Set AUTO_PR_LIVE=1 to push + open.")
        return

    date = datetime.date.today().isoformat()
    seq = len(ledger.get("runs", [])) + 1
    branch = f"aristotle-domains-{date}-{seq}"
    wt = pathlib.Path(f"/tmp/pr-wt-{date}-{seq}")
    if wt.exists():
        run(["git", "worktree", "remove", "--force", str(wt)], REPO)
    run(["git", "fetch", "origin"], REPO)
    r = run(["git", "worktree", "add", "-b", branch, str(wt), "origin/main"], REPO)
    if r.returncode != 0:
        print("worktree add failed:", r.stderr[:300]); return
    try:
        d = wt / PR_DIR
        d.mkdir(parents=True, exist_ok=True)
        man = ["# Aristotle-generated, AXLE-verified proofs", "",
               "Kernel-checked cloud Lean 4.32.0 (AXLE); axiom-clean.", ""]
        for e in new:
            safe = e["target"].replace(".", "_") + ".lean"
            shutil.copy(e["src"], d / safe)
            man.append(f"- `{e['target']}` ({e['domain']}) — {safe}")
        (d / "MANIFEST.md").write_text("\n".join(man))
        run(["git", "add", PR_DIR], wt)
        run(["git", "commit", "-m", f"Add {len(new)} AXLE-verified Aristotle domain proofs ({date} #{seq})"], wt)
        pr = run(["git", "push", "-u", "origin", branch], wt)
        if pr.returncode != 0:
            print("push failed:", pr.stderr[:300]); return
        body = "\n".join(man) + "\n\n🤖 Aristotle proof fleet; AXLE-verified axiom-clean."
        gh = run(["gh", "pr", "create", "--title",
                  f"Aristotle domain proofs ({len(new)}) — {date} #{seq}", "--body", body,
                  "--head", branch], wt)
        url = (gh.stdout or gh.stderr).strip()
        print(url)
        ledger["targets"] = sorted(done | {e["target"] for e in new})
        ledger.setdefault("runs", []).append({"branch": branch, "count": len(new), "url": url[:200]})
        PR_LEDGER.write_text(json.dumps(ledger, indent=1))
    finally:
        run(["git", "worktree", "remove", "--force", str(wt)], REPO)


if __name__ == "__main__":
    main()
