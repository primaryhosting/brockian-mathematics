import Mathlib

/-!
# Dirichlet Sum Eq Zero
Category: Characters
Target: Brockian.Characters5.dirichlet_sum_eq_zero
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- Orthogonality for multiplicative characters: a nontrivial Dirichlet character
modulo `5` with values in `ℂ` sums to zero over `ZMod 5`.
This is `MulChar.sum_eq_zero_of_ne_one`. -/
theorem dirichlet_sum_eq_zero (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    ∑ x : ZMod 5, χ x = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

end Characters5
end Brockian

