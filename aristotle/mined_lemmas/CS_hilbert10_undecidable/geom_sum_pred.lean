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

/-
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem geom_sum_pred (u k : ℕ) (hu : 1 ≤ u) : ∑ j ∈ range k, (u - 1) * u ^ j = u ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have h1 : 1 ≤ u ^ k := Nat.one_le_pow _ _ hu
      have h2 : u ^ k ≤ u ^ k * u := Nat.le_mul_of_pos_right _ hu
      have h3 : (u-1) * u^k = u^k * u - u^k := by
        have h4 : u^k * u - u^k = u^k * (u-1) := by rw [Nat.mul_sub]; simp
        rw [h4, Nat.mul_comm]
      omega

