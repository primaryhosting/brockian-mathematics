# Re-attestation regressions — lean-4.32.0 → lean-4.32.2 (2026-08-20)

The lazy re-attestation drain (`scripts/reattest_drain.py`) migrated 843 of the 854
Brockian attestations from the deprecated `lean-4.32.0` to `lean-4.32.2`. **10 modules
verified under `lean-4.32.0` but FAIL to compile under `lean-4.32.2`.** Per the drain's
honesty rule, these were **not** silently downgraded: they keep their original
`lean-4.32.0` attestation (still internally valid — `module_verified: true`, axiom-clean),
and are listed here for review. They remain claimed (imported by `Brockian.lean`) and are
still counted PROVED in `registry/theorems.json` on the strength of their `4.32.0`
attestation, which honestly records the environment it was checked under.

The `engine.audit --strict` truth gate still passes — these attestations are consistent;
env-currency is not an audit smell.

## Regressed modules (need a Lean fix for 4.32.2, or explicit quarantine)

| Module | Note |
|--------|------|
| `Dilworth` | order theory |
| `WeylConfining` | spectral / Weyl cluster |
| `WeylFourierMultiplier` | spectral / Weyl cluster |
| `WeylKatoResolventPackage` | spectral / Weyl cluster |
| `WeylMaximalMultiplication` | spectral / Weyl cluster |
| `WeylMulReal` | spectral / Weyl cluster |
| `WeylOperator` | spectral / Weyl cluster |
| `WeylOscillatorDiscrete` | spectral / Weyl cluster |
| `WeylPlancherelScaffold` | spectral / Weyl cluster |
| `WeylWeightedRellich` | spectral / Weyl cluster |

9 of 10 are the `Weyl*` spectral-theory cluster — a strong signal that a Mathlib API
change between the two toolchains (a renamed/removed lemma the cluster shares) is the
cause, not 10 independent breakages. Fixing one shared dependency likely recovers most.

## Options
1. **Fix the Lean proofs at 4.32.2** — inspect the first AXLE compile error for each (or
   the shared dependency), patch to the current Mathlib API, re-attest via
   `scripts/attest.py … --env lean-4.32.2`.
2. **Quarantine** — mark these in `provenance/verdicts.yaml` so the registry shows them as
   needing-review rather than clean PROVED, until (1) is done.

Recommendation: (1) — start with the shared Weyl dependency; it probably clears the cluster.
