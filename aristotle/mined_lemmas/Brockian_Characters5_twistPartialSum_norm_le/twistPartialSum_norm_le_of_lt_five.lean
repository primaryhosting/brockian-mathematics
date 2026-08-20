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

namespace Brockian.Characters5

open Complex

/-- The primitive fifth root of unity `ω = exp(2πi/5)`. -/

theorem twistPartialSum_norm_le_of_lt_five (N : ℕ) (h : N < 5) :
    ‖twistPartialSum N‖ ≤ 2 := by
  have hp : ∀ k : ℕ, ‖ω ^ k‖ = 1 := fun k => by rw [norm_pow, norm_omega, one_pow]
  have h5 : (1 : ℂ) + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
    have h := sum_omega_pow
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h
    linear_combination h
  interval_cases N
  · simp [twistPartialSum]
  · have h1 : twistPartialSum 1 = 1 := by
      rw [twistPartialSum_eq_geom]
      simp
    rw [h1]
    norm_num
  · have h2 : twistPartialSum 2 = 1 + ω := by
      rw [twistPartialSum_eq_geom]
      simp [Finset.sum_range_succ]
    rw [h2]
    calc ‖(1 : ℂ) + ω‖ ≤ ‖(1 : ℂ)‖ + ‖ω‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, norm_omega]; norm_num
  · have h3 : twistPartialSum 3 = -(ω ^ 3 + ω ^ 4) := by
      rw [twistPartialSum_eq_geom]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
      linear_combination h5
    rw [h3, norm_neg]
    calc ‖ω ^ 3 + ω ^ 4‖ ≤ ‖ω ^ 3‖ + ‖ω ^ 4‖ := norm_add_le _ _
      _ = 2 := by rw [hp, hp]; norm_num
  · have h4 : twistPartialSum 4 = -(ω ^ 4) := by
      rw [twistPartialSum_eq_geom]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
      linear_combination h5
    rw [h4, norm_neg, hp]
    norm_num

/-- Bounded partial sums of the zero-mean twist: `‖∑_{n < N} e(n mod 5)‖ ≤ 2` for every `N`. -/
