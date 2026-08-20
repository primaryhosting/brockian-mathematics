import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

namespace QI

open Complex Finset

/-! ## The two-qubit vectors used in the PBR argument -/

/-- The normalisation constant `1/√2`. -/

theorem pbr_supports_disjoint (M : OnticModel Λ) (l : Λ)
    (h : M.mu 0 l ≠ 0) : M.mu 1 l = 0 := by
  rcases mul_eq_zero.1 (pbr_theorem M l) with h0 | h1
  · exact absurd h0 h
  · exact h1

end QI

#print axioms QI.pbr_theorem
#print axioms QI.born_bad
#print axioms QI.xi_orthonormal
#print axioms QI.born_sum

