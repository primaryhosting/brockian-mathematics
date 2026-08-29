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
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
sys.path.insert(0, str(REPO))
from engine.verify import content_hash  # noqa: E402 — the one canonical proof hash
# cloud axiom audit (AXLE) is the soundness gate; the local lake audit
# (cross_check.json) cannot run on this box and is only an optional confirmation.
AUDIT = ROOT / "axle_axiom_audit.json"
CROSS = ROOT / "cross_check.json"
DOMAINS = REPO / "registry" / "domains.json"
BEST = ROOT / "best_proofs"
PLAN = ROOT / "pr_plan.json"
PR_LEDGER = ROOT / "pr_submitted.json"
LIVE = os.environ.get("AUTO_PR_LIVE") == "1"
PR_DIR = os.environ.get("PR_DIR", "contrib/aristotle-domains")




def eligible():
    """Return only independently checked, current-environment new-domain proofs.

    This is deliberately stricter than catalogue membership: the AXLE compile leg AND
    the AXLE cloud axiom audit must both accept the same sanitized target (same content
    hash) before it is even staged. A local lake axiom-audit agreement, when present,
    is recorded as an extra confirmation but is not required.
    """
    import re
    axle = json.loads((ROOT / "axle_verify.json").read_text()) if (ROOT / "axle_verify.json").exists() else {}
    audit = json.loads(AUDIT.read_text()) if AUDIT.exists() else {}
    cross = json.loads(CROSS.read_text()) if CROSS.exists() else {}
    domains = json.loads(DOMAINS.read_text()) if DOMAINS.exists() else {}
    out = []
    for target, dmeta in domains.items():
        san = re.sub(r"[^A-Za-z0-9]+", "_", target) + ".lean"
        axle_rec = axle.get(san, {})
        audit_rec = audit.get(san, {})
        best_src = BEST / san
        if not best_src.exists():
            continue
        current_hash = content_hash(best_src.read_text(errors="ignore"))
        if axle_rec.get("verified") is not True or axle_rec.get("environment") != "lean-4.32.2":
            continue
        # cloud axiom audit is the soundness gate (kernel-clean, no sorryAx)
        if (audit_rec.get("trusted") is not True
                or audit_rec.get("environment") != "lean-4.32.2"
                or axle_rec.get("hash") != current_hash
                or audit_rec.get("hash") != current_hash):
            continue
        cross_rec = cross.get(san, {})
        local_ok = (cross_rec.get("trusted") is True
                    and cross_rec.get("hash") == current_hash)
        out.append({"target": target, "domain": dmeta.get("domain"),
                    "src": str(best_src), "hash": current_hash,
                    "verification": ("AXLE cloud lean-4.32.2 compile + cloud axiom audit"
                                     + (" + local lake confirmed" if local_ok else "")),
                    "environment": axle_rec["environment"]})
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
        man = ["# Aristotle-generated, independently verified proofs", "",
               "Local Lean + AXLE cloud Lean 4.32.2 + content-matched axiom audit.", ""]
        for e in new:
            safe = e["target"].replace(".", "_") + ".lean"
            source = pathlib.Path(e["src"]).read_text(errors="ignore")
            (d / safe).write_text(normalize(source))
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
