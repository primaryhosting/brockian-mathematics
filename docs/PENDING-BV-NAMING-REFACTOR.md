# Pending human-scheduled refactor: "BV" naming in EquidistributionBVReduction

**Source:** third-party audit "LargeSieveLib × Brockian Mathematics × Axiom
PrimeGapsLib" (2026-08-18), §1 and §5. **Status: NOT executed — deliberately.**

## The directive

`Brockian/EquidistributionBVReduction.lean` names its hypothesis
`BVPrimePairAsymptotic`, but it is a Hardy–Littlewood **prime-pair
correlation-in-progressions** hypothesis — not the classical
Bombieri–Vinogradov theorem (single primes in APs, averaged over moduli),
which is what Axiom's `BombieriVinogradov : Prop` denotes. The two must not
share the "BV" name. Audit-recommended renames:

- `BVPrimePairAsymptotic` → `PrimePairAsymptoticInAP`
  (or `HLPrimePairAsymptoticInAP` / `UniformPrimePairsInAP`), stating
  explicitly whether the result is per fixed modulus q, uniform for
  q ≤ (log X)^A, uniform for q ≤ X^θ, or averaged over moduli.
- Conceptual target structure: distinct `ClassicalBombieriVinogradov : Prop`
  vs `PrimePairAsymptoticInAP ... : Prop` vs `UniformPrimePairsInAP ... : Prop`,
  each dependent theorem carrying its hypothesis explicitly.

## Why it was not applied on 2026-08-18

Verified/attested artifacts reference the current name:

- `registry/attestations/EquidistributionBVReduction.json` — declaration
  records for `Brockian.EquidistributionBVReduction.BVPrimePairAsymptotic`.
- `registry/theorems.json` — entries and provenance notes for the same names
  (~line 65365 onward).

Renaming the Lean declarations while the live conveyor is running would break
the attestation ↔ source correspondence (attestations are evidence about the
old names). A statement-preserving rename therefore requires a coordinated,
human-scheduled pass that updates, in one change set:

1. `Brockian/EquidistributionBVReduction.lean` (and
   `Brockian/EquidistributionUniformity.lean`, which also references the name);
2. `registry/theorems.json` entries and provenance notes;
3. `registry/attestations/EquidistributionBVReduction.json` — i.e. re-attest
   the renamed module rather than edit evidence in place;
4. any dependent modules and docs.

Until then, the honest rule stands: the `BVPrimePairAsymptotic` hypothesis is
**not** classical Bombieri–Vinogradov, and the classical-BV lane is tracked
externally in `registry/frontier/large-sieve-lib.yaml` (LargeSieveLib).
