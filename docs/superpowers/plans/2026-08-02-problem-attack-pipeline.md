# Plan: Problem Attack Pipeline v0 → v1

**Spec:** `docs/superpowers/specs/2026-08-02-problem-attack-pipeline.md`  
**Code:** `pipeline/`

## Done (v0)

- [x] Design doc
- [x] Problem card schema + Python validation
- [x] Register derivation (`derive_problem_register`) + tests
- [x] Stages: triage, attempt, decompose, attack queue
- [x] Distill size gate (10 KB) + draft ETP cheatsheet
- [x] Seed 13 cards across erdos / distillation / sair / math / physics / cs / quantum
- [x] CLI + ledger generation
- [x] 17 unit tests passing

## Next (v1)

1. `sync_erdos.py` — pull open/solved metadata from erdosproblems.com (respectful rate limits).
2. Hook `attempt --mode formalize` → `scripts/no_theater_lint.py` + `scripts/attest.py` when `formal_targets[].path` set.
3. Join pipeline ledger with `registry/theorems.json` for AXLE-backed PROVED.
4. `observatory/pipeline.html` from `pipeline/ledger/problems.json`.
5. Optional ACUTIS `GET /api/pipeline/status`.
6. Local equational T/F scorer for Stage-1 sheets (subset of ETP public set).
7. Human-gated SAIR submit checklist.

## Attack priority (current queue)

1. `distill-etp-stage1` — iterate cheatsheet, measure accuracy offline  
2. `cs-sieve-count-parity` — executable cert matching Lean  
3. `math-goldbach-local-wheels` — more finite PROVED via AXLE  
4. `erdos-28` — after statement sync, finite geometry attack  
5. Gate-1 continuous LP — continue formal (existing Brockian track)  
6. RH schema — decompose only; risk_tier 3  
