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

open scoped BigOperators

namespace Brockian
namespace Characters5

/-- Orthogonality for a nontrivial Dirichlet character mod `5` with values in `ℂ`:
the sum of its values over `ZMod 5` vanishes.  This is
`MulChar.sum_eq_zero_of_ne_one`, since `DirichletCharacter ℂ 5` is by definition
`MulChar (ZMod 5) ℂ` and `ℂ` has no zero divisors. -/

theorem dirichlet_sum_eq_zero (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    ∑ x : ZMod 5, χ x = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

end Characters5
end Brockian

