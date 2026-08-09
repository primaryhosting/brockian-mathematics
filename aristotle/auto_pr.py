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
PLAN = ROOT / "pr_plan.json"
LIVE = os.environ.get("AUTO_PR_LIVE") == "1"
PR_DIR = os.environ.get("PR_DIR", "contrib/aristotle-domains")


def eligible():
    cross = json.loads(CROSS.read_text()) if CROSS.exists() else {}
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    domains = json.loads(DOMAINS.read_text()) if DOMAINS.exists() else {}
    by_file = {f"{m['account']}_{pid[:8]}.lean": m for pid, m in ledger.items()}
    out = []
    for fname, res in cross.items():
        if res.get("trusted") is not True:
            continue
        meta = by_file.get(fname, {})
        target = meta.get("target")
        if not target or target not in domains:
            continue  # only catalogued new-domain results
        src = (MIN / fname) if (MIN / fname).exists() else (BEST / fname)
        if src.exists():
            out.append({"target": target, "domain": domains[target].get("domain"),
                        "src": str(src), "project_id": meta.get("project_id", ""),
                        "axioms": res.get("axioms", [])})
    return out


def run(cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)


def main():
    elig = eligible()
    PLAN.write_text(json.dumps({"eligible": elig, "count": len(elig), "live": LIVE}, indent=1))
    print(f"{len(elig)} kernel-trusted new-domain proofs eligible for PR "
          f"({'LIVE' if LIVE else 'DRY-RUN'})")
    for e in elig[:12]:
        print(f"  - {e['target']} ({e['domain']})")
    if not elig:
        print("nothing eligible yet (need cross_check trusted + catalogued). No PR.")
        return
    if not LIVE:
        print(f"\nDRY-RUN: plan written to {PLAN}. Set AUTO_PR_LIVE=1 to push + open the PR.")
        return

    date = datetime.date.today().isoformat()
    branch = f"aristotle-domain-proofs-{date}"
    wt = pathlib.Path(f"/tmp/pr-wt-{date}")
    if wt.exists():
        run(["git", "worktree", "remove", "--force", str(wt)], REPO)
    run(["git", "fetch", "origin"], REPO)
    r = run(["git", "worktree", "add", "-b", branch, str(wt), "origin/main"], REPO)
    if r.returncode != 0:
        print("worktree add failed:", r.stderr[:300]); return
    try:
        d = wt / PR_DIR
        d.mkdir(parents=True, exist_ok=True)
        man = ["# Aristotle-generated, kernel-trusted proofs", "",
               "Axiom-clean (only propext/Classical.choice/Quot.sound), lake-verified, cross-checked.", ""]
        for e in elig:
            safe = e["target"].replace(".", "_") + ".lean"
            shutil.copy(e["src"], d / safe)
            man.append(f"- `{e['target']}` ({e['domain']}) — {safe}")
        (d / "MANIFEST.md").write_text("\n".join(man))
        run(["git", "add", PR_DIR], wt)
        run(["git", "commit", "-m", f"Add {len(elig)} kernel-trusted Aristotle domain proofs ({date})"], wt)
        pr = run(["git", "push", "-u", "origin", branch], wt)
        if pr.returncode != 0:
            print("push failed:", pr.stderr[:300]); return
        body = "\n".join(man) + "\n\n🤖 Generated with Aristotle proof fleet; verified axiom-clean."
        gh = run(["gh", "pr", "create", "--title",
                  f"Aristotle domain proofs ({len(elig)}) — {date}", "--body", body,
                  "--head", branch], wt)
        print(gh.stdout or gh.stderr)
    finally:
        run(["git", "worktree", "remove", "--force", str(wt)], REPO)


if __name__ == "__main__":
    main()
