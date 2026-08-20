/-!
# Dirichlet Sum Eq Zero
Category: Brockian External
Target: Brockian.Characters5.dirichlet_sum_eq_zero
Statement: Multiplicative-character orthogonality mod 5: every nontrivial Dirichlet character χ mod 5 with values in ℂ satisfies Σ_{x : ZMod 5} χ x = 0.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.Characters5

/-- Orthogonality for a nontrivial Dirichlet character mod 5 with values in ℂ:
the sum of its values over `ZMod 5` vanishes. -/
theorem dirichlet_sum_eq_zero (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    ∑ x : ZMod 5, χ x = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

end Brockian.Characters5

