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

theorem pow_succ_le_descFactorial (r n : ℕ) :
    r ^ (n+1) ≤ r * r.descFactorial n + n * n * r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases Nat.lt_or_ge r (n+1) with h | h
      · have h1 : r ^ (n+1+1) ≤ ((n+1)*(n+1)) * r^(n+1) := by
          rw [pow_succ']
          exact Nat.mul_le_mul_right _ (by nlinarith)
        omega
      · rw [Nat.descFactorial_succ]
        set D : ℤ := (r.descFactorial n : ℤ) with hD
        set X : ℤ := (r:ℤ)^n with hX
        have hXnn : (0:ℤ) ≤ X := by positivity
        have hr : (0:ℤ) ≤ (r:ℤ) := Int.natCast_nonneg r
        have hn : (0:ℤ) ≤ (n:ℤ) := Int.natCast_nonneg n
        have hDnn : (0:ℤ) ≤ D := Int.natCast_nonneg _
        have hrn : (n:ℤ) ≤ (r:ℤ) := by
          exact_mod_cast le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self n) h)
        have ihz : (r:ℤ) * X ≤ (r:ℤ) * D + (n:ℤ) * n * X := by
          have h2 : ((r ^ (n+1) : ℕ) : ℤ) ≤ ((r * r.descFactorial n + n * n * r ^ n : ℕ) : ℤ) :=
            Int.ofNat_le.mpr ih
          push_cast at h2
          rw [pow_succ'] at h2
          linarith [h2]
        have e1 : ((r:ℤ) - n) * ((r:ℤ) * X - (n:ℤ)*n*X) ≤ ((r:ℤ) - n) * ((r:ℤ) * D) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have key : (r:ℤ) * ((r:ℤ) * X)
            ≤ (r:ℤ) * (((r:ℤ) - n) * D) + ((n:ℤ)+1)*((n:ℤ)+1)*((r:ℤ)*X) := by
          nlinarith [e1, mul_nonneg (mul_nonneg hn (mul_nonneg hn hn)) hXnn,
            mul_nonneg (mul_nonneg hr hn) hXnn, mul_nonneg hr hXnn]
        have hcast : ((r - n : ℕ) : ℤ) = (r:ℤ) - n := by
          push_cast [Nat.cast_sub (by exact_mod_cast hrn)]; ring
        have final : ((r ^ (n+1+1) : ℕ) : ℤ) ≤
            ((r * ((r - n) * r.descFactorial n) + (n+1) * (n+1) * r ^ (n+1) : ℕ) : ℤ) := by
          push_cast [hcast]
          rw [pow_succ', pow_succ']
          rw [hD, hX] at key
          linarith [key]
        exact_mod_cast final

/-- Davis' formula for the factorial: `n! = r^n / choose r n` once `r` is large. -/
