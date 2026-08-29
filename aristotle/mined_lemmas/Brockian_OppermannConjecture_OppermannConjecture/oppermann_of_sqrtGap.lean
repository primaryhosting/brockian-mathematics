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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


theorem oppermann_of_sqrtGap (H : SqrtGapHypothesis) : OppermannConjecture := by
  intro n hn
  by_cases hsmall : n ≤ 200
  · exact oppermann_of_le_200 n hn hsmall
  have h33 : 33 ≤ n := by omega
  constructor
  · have hk : (n - 1) * (n - 1) ≤ n * (n - 1) :=
      Nat.mul_le_mul_right _ (Nat.sub_le n 1)
    have hm : 1000 ≤ n * (n - 1) :=
      Nat.le_trans (by decide) (Nat.mul_le_mul h33 (by omega : 32 ≤ n - 1))
    obtain ⟨p, hp, hp1, hp2⟩ := H (n * (n - 1)) (n - 1) hm hk
    exact ⟨p, hp, hp1, Nat.lt_trans hp2 (sq_pred_lt n (by omega))⟩
  · have hm : 1000 ≤ n * n := Nat.le_trans (by decide) (Nat.mul_le_mul h33 h33)
    obtain ⟨p, hp, hp1, hp2⟩ := H (n * n) n hm (Nat.le_refl _)
    refine ⟨p, hp, hp1, ?_⟩
    rw [Nat.mul_succ]
    exact hp2

/-! ## Consequences -/

/-- Oppermann's conjecture implies Legendre's conjecture. -/
