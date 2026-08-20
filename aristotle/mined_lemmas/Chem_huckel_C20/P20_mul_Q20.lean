import Mathlib

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

namespace Chem

open Complex Polynomial Matrix

/-- The commutative ring structure on `Fin 20 = ZMod 20`, used for index arithmetic. -/
noncomputable instance : CommRing (Fin 20) := inferInstanceAs (CommRing (ZMod 20))

/-- A primitive 20-th root of unity. -/

lemma P20_mul_Q20 : P20 * Q20 = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : Fin 20, P20 i k * Q20 k j = (20 : ℂ)⁻¹ * zeta (k * (i - j)) := by
    intro k
    simp only [P20, Q20]
    rw [show k * (i - j) = i * k + -(k * j) by ring, zeta_add]
    ring
  simp only [h, ← Finset.mul_sum, zeta_sum]
  rw [Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; norm_num
  · rw [if_neg (by simpa [sub_eq_zero] using hij), if_neg hij, mul_zero]

