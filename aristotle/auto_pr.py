#!/usr/bin/env python3
"""Open a proof PR containing only exact V5-gated selected artifacts.

Dry-run by default.  V5 means local pinned Lean + AXLE + expected-target match + a
saved standard-axiom report.  The exact ``best_proofs`` bytes are shipped; annotated
preview copies are deliberately excluded from the release path.
"""
import datetime
import json
import os
import pathlib
import shutil
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
RECON = REPO / "pipeline/ledger/reviews/2026-08-13-aristotle-runtime-reconciliation.json"
DOMAINS = REPO / "registry" / "domains.json"
BEST = ROOT / "best_proofs"
PLAN = ROOT / "pr_plan.json"
PR_LEDGER = ROOT / "pr_submitted.json"
LIVE = os.environ.get("AUTO_PR_LIVE") == "1"
PR_DIR = os.environ.get("PR_DIR", "contrib/aristotle-domains")


def eligible():
    reconciliation = json.loads(RECON.read_text()) if RECON.exists() else {"targets": []}
    domains = json.loads(DOMAINS.read_text()) if DOMAINS.exists() else {}
    output = []
    for record in reconciliation.get("targets", []):
        if record.get("promotion_allowed") is not True:
            continue
        target = record["target"]
        selected = record.get("selected") or {}
        artifact = selected.get("artifact_file")
        source = BEST / artifact if artifact else None
        if target not in domains or not source or not source.exists():
            continue
        output.append(
            {
                "target": target,
                "domain": domains[target].get("domain"),
                "artifact_file": artifact,
                "source": str(source),
                "verification": record.get("verification_detail"),
                "verification_level": "V5",
            }
        )
    return output


def run(command, cwd):
    return subprocess.run(command, cwd=cwd, capture_output=True, text=True)


def main():
    candidates = eligible()
    PLAN.write_text(json.dumps({"eligible": candidates, "count": len(candidates), "live": LIVE}, indent=1))
    ledger = json.loads(PR_LEDGER.read_text()) if PR_LEDGER.exists() else {"targets": [], "runs": []}
    done = set(ledger.get("targets", []))
    new = [candidate for candidate in candidates if candidate["target"] not in done]
    print(f"{len(candidates)} V5 eligible; {len(new)} new ({'LIVE' if LIVE else 'DRY-RUN'})")
    if not new:
        return
    if not LIVE:
        print("review the V5 reconciliation and set AUTO_PR_LIVE=1 intentionally")
        return

    date = datetime.date.today().isoformat()
    sequence = len(ledger.get("runs", [])) + 1
    branch = f"aristotle-v5-{date}-{sequence}"
    worktree = pathlib.Path(f"/tmp/aristotle-v5-{date}-{sequence}")
    if worktree.exists():
        run(["git", "worktree", "remove", "--force", str(worktree)], REPO)
    run(["git", "fetch", "origin"], REPO)
    created = run(["git", "worktree", "add", "-b", branch, str(worktree), "origin/main"], REPO)
    if created.returncode != 0:
        print("worktree add failed:", created.stderr[:500])
        return
    try:
        destination = worktree / PR_DIR
        destination.mkdir(parents=True, exist_ok=True)
        manifest = [
            "# Aristotle-generated, V5-gated proof artifacts",
            "",
            "Exact bytes independently checked by local pinned Lean and AXLE, with expected-target matching and saved axiom reports.",
            "",
        ]
        for candidate in new:
            shutil.copy(candidate["source"], destination / candidate["artifact_file"])
            manifest.append(
                f"- `{candidate['target']}` ({candidate['domain']}) — {candidate['artifact_file']}"
            )
        (destination / "MANIFEST.md").write_text("\n".join(manifest) + "\n")
        run(["git", "add", PR_DIR], worktree)
        committed = run(
            ["git", "commit", "-m", f"Add {len(new)} V5-gated Aristotle proof artifacts"],
            worktree,
        )
        if committed.returncode != 0:
            print("commit failed:", committed.stderr[:500])
            return
        pushed = run(["git", "push", "-u", "origin", branch], worktree)
        if pushed.returncode != 0:
            print("push failed:", pushed.stderr[:500])
            return
        body = "\n".join(manifest) + "\n\nNo mathematical-novelty claim is made."
        opened = run(
            [
                "gh",
                "pr",
                "create",
                "--title",
                f"V5-gated Aristotle proof artifacts ({len(new)})",
                "--body",
                body,
                "--head",
                branch,
                "--draft",
            ],
            worktree,
        )
        url = (opened.stdout or opened.stderr).strip()
        print(url)
        ledger["targets"] = sorted(done | {candidate["target"] for candidate in new})
        ledger.setdefault("runs", []).append({"branch": branch, "count": len(new), "url": url[:300]})
        PR_LEDGER.write_text(json.dumps(ledger, indent=1) + "\n")
    finally:
        run(["git", "worktree", "remove", "--force", str(worktree)], REPO)


if __name__ == "__main__":
    main()
