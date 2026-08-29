import Mathlib

/-!
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
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

/-- A primitive fifth root of unity. -/

theorem sum_e_univ : ∑ c : ZMod 5, e c = 0 := by
  have h : ∑ i ∈ Finset.range 5, omega ^ i = 0 :=
    omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one] at h
  show ∑ c : Fin 5, e c = 0
  rw [Fin.sum_univ_five]
  simpa [e, ZMod.val] using h

/-- Orthogonality relation for the character `e`. -/
