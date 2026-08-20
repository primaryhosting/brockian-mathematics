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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` sending `a` to `ω ^ a`. -/

lemma sum_e_univ : ∑ a : ZMod 5, e a = 0 := by
  have h : ∑ i ∈ Finset.range 5, ω ^ i = 0 :=
    omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  have h2 : ∑ a : ZMod 5, e a = ∑ i ∈ Finset.range 5, ω ^ i := by
    show ∑ a : Fin 5, ω ^ (ZMod.val (n := 5) a) = _
    simp [Fin.sum_univ_five, Finset.sum_range_succ, ZMod.val]
  rw [h2, h]

/-- Orthogonality relation for the character `e`. -/
