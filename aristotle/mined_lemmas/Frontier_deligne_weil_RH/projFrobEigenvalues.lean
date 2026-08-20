/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization notes

Mathlib (as of the pinned commit) contains no development of étale cohomology, Weil
cohomology theories, or zeta functions of varieties over finite fields, so no existing

def projFrobEigenvalues (q n w : ℕ) : Multiset ℂ :=
  if w % 2 = 0 ∧ w / 2 ≤ n then {(q : ℂ) ^ (w / 2)} else 0

/-- The Lefschetz trace formula: the number of `F_{q^m}`-points of the variety is the
alternating sum of the traces of the `m`-th power of Frobenius on cohomology. -/
