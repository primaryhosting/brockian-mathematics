# Problem Attack Pipeline

Multi-domain process for attacking **Erdős problems**, **SAIR distillation challenges**, **SAIR.foundation** programs, and open problems in **mathematics, physics, computer science, and quantum physics**.

Generalizes the Brockian method:

> intake → triage → decompose → attack/refute → verify → **derive register** → distill → publish (no theater)

Design: [`docs/superpowers/specs/2026-08-02-problem-attack-pipeline.md`](../docs/superpowers/specs/2026-08-02-problem-attack-pipeline.md)

## Quick start

From repo root (`brockian-mathematics/`):

```bash
# Seed starter catalogs (all domains)
python3 -m pipeline.scripts.seed_catalog

# List / filter
python3 -m pipeline.scripts.pipeline_cli list
python3 -m pipeline.scripts.pipeline_cli list --domain erdos --status open

# Ranked attack queue
python3 -m pipeline.scripts.pipeline_cli queue --limit 15

# Triage one problem
python3 -m pipeline.scripts.pipeline_cli triage distill-etp-stage1

# Record an attempt
python3 -m pipeline.scripts.pipeline_cli attempt distill-etp-stage1 \
  --mode distill --result partial --note "draft etp_v0 sheet" --agent grok

# Cheatsheet size gate (SAIR Stage 1 ≤ 10KB)
python3 -m pipeline.scripts.pipeline_cli distill-check pipeline/distill/cheatsheets/etp_v0.txt

# Rebuild human ledger
python3 -m pipeline.scripts.pipeline_cli ledger
```

## Registers (problem-level)

Derived — never hand-assert **PROVED** without independent formal verification:

| Register | Meaning |
|----------|---------|
| OPEN | No closing artifact |
| SCAFFOLD | Defs / schemas only |
| CONDITIONAL | Under named hypothesis |
| COMPUTATION | Finite / numeric cert |
| DISTILLED | Cheatsheet passed harness gates |
| PROVED | Lean axioms clean + AXLE (or equiv.) |
| REFUTED | Certified counterexample |
| LITERATURE | External solution accepted (not our formal proof) |
| BLOCKED | Theater / dual-prover disagreement / policy |

Theorem-level PROVED for Lean stays in `registry/theorems.json` via existing `scripts/attest.py`.

## Layout

```
pipeline/
  catalog/<domain>/*.json   # problem cards
  core/                     # schema, ledger, stages, triage
  adapters/                 # domain helpers
  distill/cheatsheets/      # SAIR-style sheets
  ledger/                   # generated LEDGER.md + problems.json
  scripts/pipeline_cli.py
  tests/
```

## Domains

| Domain | Catalog | Primary backend |
|--------|---------|-----------------|
| erdos | `catalog/erdos/` | literature + hybrid formal/compute |
| distillation | `catalog/distillation/` | distillation_harness |
| sair | `catalog/sair/` | literature / meta tracker |
| math | `catalog/math/` | lean_axle → Brockian |
| physics | `catalog/physics/` | lean_axle / hybrid |
| cs | `catalog/cs/` | compute + tests |
| quantum | `catalog/quantum/` | lean_axle |

## Tests

```bash
python3 -m pytest pipeline/tests -q
```

## Non-negotiables

1. No RH / Goldbach / millennium overclaim.
2. External “solved” Erdős → **LITERATURE** unless we re-formalize.
3. Distillation competition submit only after human review.
4. Dual-prover disagreement → **BLOCKED**.
