# Re-attestation "regressions" — RESOLVED (2026-08-20)

The lean-4.32.0 → lean-4.32.2 attestation drain flagged 10 modules as failing at the new
env (`Dilworth` + the 9-module `Weyl*` spectral cluster). **All 10 were FALSE regressions:
a probe-construction bug in `scripts/attest.py`, not broken mathematics.** All 10 now
re-attest clean at lean-4.32.2; the entire 854-module corpus is on one environment and
`engine.audit --strict` passes.

## Root cause (two compounding bugs, both in the axiom probe)

The proofs compiled fine; the failures were on the appended `#print axioms` probe lines
(`error: unknown constant …`). Two issues in how `attest.py` built the probe:

1. **Partial qualification via `open`.** It used `open {module} in #print axioms {short}`,
   where `{module}` was the attestation's (file-stem-derived) module field — often not the
   real namespace (`Brockian.WeylOperator` vs the true `Brockian.Weyl.Operator`), and it
   does not reach declarations in *nested* namespaces (`…Operator.IsSymmetric.foo`).
   lean-4.32.0 resolved these loosely; lean-4.32.2 tightened `#print axioms` name
   resolution and they became `unknown constant`. Fixed by building probes from
   **fully-qualified names** via `engine.verify.qualified_decls` (no `open`), matching the
   approach already used by `axle_axiom_audit.py`.

2. **Namespace-prefixed `def` misclassified as a theorem.** `_kind_of` matched only bare
   names after `def`/`abbrev`, so `def Factorization.ofCompact` fell through to the
   "theorem" default and got probed with `#print axioms` (a def is not a proof term and is
   absent from the theorem/lemma name set) → the whole probe failed on one bad name. Fixed
   by allowing an optional dotted prefix in the `def`/`abbrev`/`structure` classifier.

## Novel points

- The toolchain bump's user-visible effect here was on the **attestation artifact**
  (`#print axioms` name resolution), **not** on any theorem's provability — a clean
  instance of the *soundness vs. attestability* gap in machine-checked mathematics.
- The cluster was a **naming-idiom correlation**, not a mathematical one: failure ⟺ audited
  declarations in a nested namespace (`IsSymmetric`/`Adjoint`/`ChainColoring`); the `Weyl*`
  modules simply share that idiom.
- The drain's honesty rule (never silently downgrade a regressed module) was exactly right:
  it preserved 10 genuinely-sound modules and surfaced a tooling bug instead of corrupting
  the registry with false failures.

## Effect on the registry

Re-attesting the 10 with the fixed classifier also corrected ~9 declarations from
theorem→def (`def Namespace.name` that had been mislabeled), so PROVED moved 11,124 → 11,115
and DEFINITION 628 → 637 — an honesty correction, not a loss of proofs.
