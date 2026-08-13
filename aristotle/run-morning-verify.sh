#!/bin/zsh
export PATH="/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin:$HOME/.local/bin:$PATH"
set -a
[[ -f "$HOME/.openclaw/vault-bridges.env" ]] && source "$HOME/.openclaw/vault-bridges.env"
set +a
: "${SOLVER_NOTIFY_TO:=chrisbrock54@gmail.com}"; export SOLVER_NOTIFY_TO
REPO_ROOT="${BROCKIAN_REPO:-$HOME/Projects/brockian-mathematics}"
cd "$REPO_ROOT" || exit 1

# Never stack local Lean jobs. Harvest remains read-only and may still run.
if pgrep -f verify_stage.py >/dev/null; then
  echo "verify_stage already running; harvest only"
  /opt/homebrew/bin/python3 aristotle/harvest_proofs.py
  HARVEST_ALL_MAX=80 /opt/homebrew/bin/python3 aristotle/harvest_all.py
  exit 0
fi

/opt/homebrew/bin/python3 aristotle/harvest_proofs.py
HARVEST_ALL_MAX=2400 /opt/homebrew/bin/python3 aristotle/harvest_all.py
/opt/homebrew/bin/python3 aristotle/verify_stage.py
/opt/homebrew/bin/python3 aristotle/select_best.py
AXLE_MAX=40 /opt/homebrew/bin/python3 aristotle/axle_verify.py
AXIOM_MAX=40 /opt/homebrew/bin/python3 aristotle/axiom_report.py
/opt/homebrew/bin/python3 aristotle/reconcile_proofs.py
/opt/homebrew/bin/python3 aristotle/catalogue_domains.py
/opt/homebrew/bin/python3 aristotle/lemma_mine.py
/opt/homebrew/bin/python3 aristotle/reduction_tracker.py
CROSS_MAX=6 /opt/homebrew/bin/python3 aristotle/cross_check.py
/opt/homebrew/bin/python3 aristotle/minimize_proofs.py
/opt/homebrew/bin/python3 aristotle/annotate_headers.py

# Publication automation is deliberately paused during consolidation. A human may
# run auto_pr.py after reviewing the V5 reconciliation and saved axiom reports.
AUTO_PR_LIVE=0 /opt/homebrew/bin/python3 aristotle/auto_pr.py
/opt/homebrew/bin/python3 aristotle/observatory.py

git add aristotle/harvest_ledger.json aristotle/submitted_night.json \
  aristotle/harvest_report.md aristotle/harvest_100 aristotle/best_proofs \
  aristotle/axle_verify.json aristotle/axiom_reports registry/domains.json \
  pipeline/ledger/reviews/2026-08-13-aristotle-runtime-reconciliation.json \
  pipeline/ledger/reviews/2026-08-13-aristotle-runtime-reconciliation.md
if ! git diff --cached --quiet; then
  git commit -m "aristotle: checkpoint consolidated harvest and verification evidence"
  git push origin HEAD:top3-aristotle-ledger-2026-08-11
fi
