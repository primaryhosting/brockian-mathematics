# Off-Mini Mathlib / Physlib harvest runbook (Grok — step 3)

**Why off-Mini:** Mac Mini is env-blocked for full Mathlib builds (16 GB RAM thrash; disk often ~95–97% full / ~8 GB free).  
Extractor docs require a box with `lake exe cache get` oleans present.

## Already verified on Mini (2026-08-02 — Grok pass 1+2+3)

```bash
python3 scripts/harvest/run_extract.py --self-test   # PASSED
python3 scripts/harvest/ingest.py --selftest         # PASSED
python3 scripts/export_public_registry.py            # brockian-only public registry OK (PROVED=1832)
```

```bash
# print exact extract command + Lean extractor path
python3 scripts/harvest/run_extract.py --run-cmd
python3 scripts/harvest/run_extract.py --print-lean
```

## Exact off-Mini commands

On a **Linux CI / cloud / larger Mac** with Lean 4.32 + Mathlib cache:

```bash
git clone https://github.com/primaryhosting/brockian-mathematics.git  # or rsync this repo
cd brockian-mathematics
# Pin matches Physlib: leanprover/lean4:v4.32.0

# Option A — Mathlib only (via this project's lake Mathlib dep)
lake exe cache get
mkdir -p harvest
lake env lean --run scripts/harvest/ExtractEnv.lean > harvest/mathlib.ndjson

# Option B — Mathlib + Physlib (requires Physlib as a lake dep or sibling import path)
# Recommended: checkout physlib at same Lean pin, then either:
#   - add require physlib to a throwaway lakefile branch, OR
#   - run extractor from a physlib checkout with a copy of ExtractEnv.lean
lake env lean --run scripts/harvest/ExtractEnv.lean Mathlib > harvest/mathlib.ndjson

# Physlib: clone and build QuantumInfo (lighter than full Physlib if needed)
git clone https://github.com/leanprover-community/physlib.git ~/src/physlib
cd ~/src/physlib && lake exe cache get && lake build QuantumInfo
# Then run ExtractEnv adapted to import QuantumInfo roots, OR extend ExtractEnv CLI roots
```

Ship NDJSON back to Mini (do **not** re-run extract on Mini):

```bash
rsync -avz user@bigbox:~/brockian-mathematics/harvest/*.ndjson \
  ~/Projects/brockian-mathematics/harvest/
```

## On Mini — validate + ingest

```bash
cd ~/Projects/brockian-mathematics
python3 scripts/harvest/run_extract.py harvest/mathlib.ndjson
python3 scripts/harvest/ingest.py harvest/mathlib.ndjson --source mathlib
# optional: physlean dump with --source physlean

# After ingest, regenerate public registry (split-by-source will show mathlib/physlean facets)
python3 scripts/export_public_registry.py
cp torus/public/verified-registry.json deploy/torus-lovable/public/
```

## Honesty rules

- Indexed Mathlib/Physlib decls: `verified_by: mathlib-kernel` (or physlib-kernel) — **not** Brockian AXLE PROVED.
- UI must **split counts by source** (already in exporter + VerifiedClaim design).
- Exclude `sorryAx` / nonstandard axioms from clean PROVED-eligible set (run_extract enforces).

## Disk note (Mini 2026-08-02 evening)

`df` showed ~**97% full / ~7.8 GB free**. Free more space before large NDJSON ingest if harvest dumps are multi-GB.

## Status this session (Grok 1+2+3)

| Step | Result |
|------|--------|
| Self-test extract | **PASSED** |
| Self-test ingest | **PASSED** |
| Full Mathlib extract on Mini | **SKIPPED** (by design + disk/RAM) |
| Off-Mini extract | **Operator/CI required** — commands above |
| Public brockian export | **DONE** → `torus/public/verified-registry.json` + `deploy/torus-lovable/public/` |
