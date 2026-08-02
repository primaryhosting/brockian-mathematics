# Plan: Settle Factory Wiring (2026-08-02)

Status: **docs + print-only bridge landed** (Agent SETTLE-WIRE). No gen_registry rewrite; no git commit.

## Existing factory (do not reimplement)

- `scripts/settle.py` (commit `63e8e09`) — certificate factory
- `scripts/attest.py` + `scripts/gen_registry.py` — committed attestation → theorem registry
- `pipeline/core/ledger.py` — problem-level REFUTED / PROVED / BLOCKED

## Landed this pass

| Deliverable | Path |
|-------------|------|
| Operator runbook | `docs/SETTLE-FACTORY.md` |
| Print-only command bridge | `scripts/pipeline_attest_bridge.py` |
| Bridge tests | `tests/test_pipeline_attest_bridge.py` |
| This plan | `docs/superpowers/plans/2026-08-02-settle-factory-wiring.md` |

**Not written:** `scripts/gen_program_report.py` (reserved for Agent REPORT / concurrent ownership).

## Next slices (safe order)

1. Optional `pipeline_cli attempt --wire-attest` that shells to printed plan steps only when `formal_targets[].path` is set (still no silent PROVED).
2. `join-cert` helper: read `registry/certificates/X.json` → append pipeline attempt with correct result flags.
3. Stage-2 SAIR packaging checklist under `pipeline/distill/` (human submit gate).
4. Theorem-level REFUTED provenance only if product needs it (problem-level REFUTED already works).

## How to run

```bash
python3 scripts/pipeline_attest_bridge.py Brockian/Foo.lean --pipeline-id distill-etp-stage2
python3 -m pytest tests/test_pipeline_attest_bridge.py -q
# with AXLE_API_KEY:
python3 scripts/settle.py Brockian/Foo.lean --env lean-4.32.0
```
