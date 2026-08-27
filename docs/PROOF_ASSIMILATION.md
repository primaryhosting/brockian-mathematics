# Proof assimilation and solver steering

The Aristotle fleet can return several proofs per hour. Raw throughput is not the
objective: the system must compare attempts, promote only independently verified
work, and spend the next proof-search call on results that unlock downstream work.

## Data flow

1. `aristotle/harvest_ledger.json` is the attempt ledger. `PROVED` in this file means
   proof **candidate**, never a public theorem.
2. `aristotle/select_best.py` chooses among same-target attempts. It prefers a
   hash-matched verified candidate, then compile status, clean syntax, and size. A
   candidate that failed a hash-matched AXLE or axiom check loses to an untested
   alternative on the next pass.
3. AXLE compile results, axiom audits, and local Lean status remain separate,
   hash-bound receipts.
4. `scripts/proof_assimilation.py` joins those receipts with the canonical theorem
   registry and frontier targets. It emits a sanitized GitHub ledger and review page.
5. Only `scripts/gen_registry.py` derives `registry/theorems.json`. Assimilation never
   writes the registry or changes a theorem statement.

## Compounding-value score

The steering score begins with the existing editorial score and then uses explicit,
reviewable metadata:

- `depends_on`: declarations that must already be PROVED;
- `unlocks`: downstream frontier targets made attackable by this theorem;
- `consumers`: known modules or results that reuse it;
- `target_class` / `foundational`: API, library, parser, transfer, or bridge work;
- proofs already in hand and their current verification gate;
- failed attempts and estimated cost.

The score changes **priority only**. It never changes whether a proof counts. If two
backends return opposite polarities, the target is disputed and no winner is promoted.

## Run locally or in an AutoLab wave

```bash
python3 scripts/proof_assimilation.py
```

Outputs:

- `research/proof_assimilation.json` — machine-readable candidates and steering queue;
- `research/proof_assimilation.REVIEW.md` — human review surface.

Missing hourly ledgers are allowed, so GitHub CI can still validate the code and rank
registry targets. AutoLab runs should supply or inherit the live ledgers before using
the report to submit new solver jobs.

## GitHub promotion

The required `promotion-gate` checks policy, registry derivation, Python tests, and
every changed Lean module. A separate scheduled full-corpus audit remains honest about
legacy baseline failures without blocking unrelated proof-assimilation infrastructure.
GitHub `main` should require the promotion gate and disallow force pushes.
