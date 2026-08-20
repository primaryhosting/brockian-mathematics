/-
# Dirichlet Sum Eq Zero
Category: Characters
Target: Brockian.Characters5.dirichlet_sum_eq_zero
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian.Characters5

/-- Orthogonality for multiplicative characters mod 5: any nontrivial Dirichlet character
`χ` mod `5` with values in `ℂ` has vanishing total sum over `ZMod 5`. -/
theorem dirichlet_sum_eq_zero (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    ∑ x : ZMod 5, χ x = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

end Brockian.Characters5

