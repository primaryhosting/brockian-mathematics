/-
# Dirichlet Sum Eq Zero
Category: Characters
Target: Brockian.Characters5.dirichlet_sum_eq_zero
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Dirichlet Sum Eq Zero
Category: Characters
Target: Brockian.Characters5.dirichlet_sum_eq_zero
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.Characters5

/-- Orthogonality mod 5: every nontrivial Dirichlet character `χ` mod `5` with values
in `ℂ` satisfies `∑ x : ZMod 5, χ x = 0`. -/
theorem dirichlet_sum_eq_zero (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    ∑ x : ZMod 5, χ x = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

end Brockian.Characters5

