#!/usr/bin/env bash
# Apply the four known layout repairs on a new review branch. Never merge or
# rewrite attestations. Run the kernel checker and attach receipts afterwards.
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"
if [[ -n "$(git status --porcelain)" ]]; then
  echo 'Start from a clean worktree so the repair commit contains only these fixes.' >&2
  exit 1
fi
review_branch=${1:-review/import-order-repair}
git check-ref-format --branch "$review_branch" >/dev/null
git switch -c "$review_branch"

modules=(
  Brockian/SieveSpectrumDeletion.lean
  Brockian/SieveSpectrumCounts.lean
  Brockian/SieveSpectrumBlocks.lean
  Brockian/OddPerfectThreePrimes.lean
)
python3 scripts/lean_layout_lint.py --fix "${modules[@]}"
python3 scripts/lean_layout_lint.py "${modules[@]}"
git diff --check
if git diff --quiet -- "${modules[@]}"; then
  echo 'The four modules already have valid import order; no repair commit is needed.'
  exit 0
fi
git add -- "${modules[@]}"
git commit -m 'Repair import placement in four Lean modules'
echo 'Review branch prepared. Compile the exact sources and attach fresh receipts before merge.'
echo 'python3 scripts/check_structural_core.py --output /tmp/structural-receipts'
