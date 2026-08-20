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

lemma zeta_sum (c : Fin 20) : (∑ k : Fin 20, zeta (k * c)) = if c = 0 then 20 else 0 := by
  simp only [zeta_mul]
  rw [Fin.sum_univ_eq_sum_range (fun n => zeta c ^ n) 20]
  by_cases hc : c = 0
  · subst hc
    simp [zeta_zero]
  · have h1 : zeta c ≠ 1 := fun h => hc ((zeta_eq_one_iff c).1 h)
    have h20 : zeta c ^ (20 : ℕ) = 1 := by
      simp only [zeta, ← pow_mul]
      rw [mul_comm, pow_mul, w_pow_20, one_pow]
    rw [geom_sum_eq h1, h20, sub_self, zero_div, if_neg hc]

