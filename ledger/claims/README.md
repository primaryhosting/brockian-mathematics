# Claim registry

`claims.json` is the human-authored concordance between a public mathematical claim,
its exact Lean declaration, and its evidence bundle. `schema.json` specifies the
portable record shape. The generated table is `docs/CLAIM_STATUS.md`.

## Rules

- A status is not a marketing label. It is derived from the fields in the record.
- `#print axioms` reports kernel axioms only; it does **not** list explicit theorem
  premises. Every conditional claim must therefore list `hypotheses_carried`.
- V4 requires a pinned local build, source hash, theorem-signature hash, and raw
  axiom-report hash. V5 additionally requires an independent pinned reproduction.
- A claim using `UniformPrimePairsInAP` must name the modulus range `Q(X)`.
- The registry may describe a stale or quarantined artifact, but it may not promote it.

## Commands

```bash
python3 scripts/validate_claims.py
python3 scripts/gen_claim_status.py
```
