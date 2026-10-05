import Mathlib

/-!
# Twist Partial Sum Norm Le
Category: Characters
Target: Brockian.Characters5.twistPartialSum_norm_le
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

namespace Brockian.Characters5

/-- The primitive fifth root of unity `exp(2πi/5)`. -/

theorem twistPartialSum_norm_le_small (N : ℕ) (hN : N < 5) : ‖twistPartialSum N‖ ≤ 2 := by
  have hsum : (1 : ℂ) + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
    have := sum_omega_pow
    simp [Finset.sum_range_succ] at this
    linear_combination this
  have h1 : ‖omega ^ 3‖ = 1 := by rw [norm_pow, norm_omega, one_pow]
  have h2 : ‖omega ^ 4‖ = 1 := by rw [norm_pow, norm_omega, one_pow]
  interval_cases N <;>
    simp only [twistPartialSum_eq, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  · norm_num
  · rw [norm_one]; norm_num
  · calc ‖(1 : ℂ) + omega‖ ≤ ‖(1 : ℂ)‖ + ‖omega‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, norm_omega]; norm_num
  · have : (1 : ℂ) + omega + omega ^ 2 = -(omega ^ 3 + omega ^ 4) := by linear_combination hsum
    rw [this, norm_neg]
    calc ‖omega ^ 3 + omega ^ 4‖ ≤ ‖omega ^ 3‖ + ‖omega ^ 4‖ := norm_add_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  · have : (1 : ℂ) + omega + omega ^ 2 + omega ^ 3 = -(omega ^ 4) := by linear_combination hsum
    rw [this, norm_neg, h2]
    norm_num

/-- Bounded partial sums of the zero-mean twist: `‖∑_{n < N} e(n mod 5)‖ ≤ 2`. -/
