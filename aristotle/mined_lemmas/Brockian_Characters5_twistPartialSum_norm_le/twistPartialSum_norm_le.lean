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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = e^{2πi/5}`. -/

theorem twistPartialSum_norm_le (N : ℕ) : ‖twistPartialSum N‖ ≤ 2 := by
  rw [twistPartialSum_mod]
  have hlt : N % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h5 : ∑ j ∈ Finset.range 5, omega ^ j = 0 := sum_omega_pow
  have hpow : ∀ k : ℕ, ‖omega ^ k‖ = 1 := by
    intro k; rw [norm_pow, norm_omega, one_pow]
  interval_cases h : (N % 5)
  · simp [twistPartialSum_eq]
  · rw [twistPartialSum_eq]
    norm_num
  · rw [twistPartialSum_eq]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    calc ‖omega ^ 0 + omega ^ 1‖ ≤ ‖omega ^ 0‖ + ‖omega ^ 1‖ := norm_add_le _ _
      _ = 2 := by rw [hpow, hpow]; norm_num
  · rw [twistPartialSum_eq]
    have hs : ∑ n ∈ Finset.range 3, omega ^ n = -(omega ^ 3 + omega ^ 4) := by
      have := h5
      simp [Finset.sum_range_succ] at this ⊢
      linear_combination this
    rw [hs, norm_neg]
    calc ‖omega ^ 3 + omega ^ 4‖ ≤ ‖omega ^ 3‖ + ‖omega ^ 4‖ := norm_add_le _ _
      _ = 2 := by rw [hpow, hpow]; norm_num
  · rw [twistPartialSum_eq]
    have hs : ∑ n ∈ Finset.range 4, omega ^ n = -(omega ^ 4) := by
      have := h5
      simp [Finset.sum_range_succ] at this ⊢
      linear_combination this
    rw [hs, norm_neg, hpow]
    norm_num

end Characters5
end Brockian

