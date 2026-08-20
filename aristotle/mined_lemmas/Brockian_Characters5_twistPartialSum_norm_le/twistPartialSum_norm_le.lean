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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity, `ω = exp(2πi/5)`. -/

theorem twistPartialSum_norm_le (N : ℕ) : ‖twistPartialSum N‖ ≤ 2 := by
  rw [twistPartialSum_mod]
  have hlt : N % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h1 : ‖omega‖ = 1 := norm_omega
  interval_cases h : (N % 5) <;>
    simp only [twistPartialSum_eq, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero,
      zero_add, pow_one]
  · norm_num
  · norm_num
  · calc ‖(1 : ℂ) + omega‖ ≤ ‖(1 : ℂ)‖ + ‖omega‖ := norm_add_le _ _
      _ ≤ 2 := by rw [h1, norm_one]; norm_num
  · have hrw : (1 : ℂ) + omega + omega ^ 2 = -(omega ^ 3 + omega ^ 4) := by
      linear_combination omega_sum_expand
    rw [hrw, norm_neg]
    calc ‖omega ^ 3 + omega ^ 4‖ ≤ ‖omega ^ 3‖ + ‖omega ^ 4‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_pow, norm_pow, h1]; norm_num
  · have hrw : (1 : ℂ) + omega + omega ^ 2 + omega ^ 3 = -(omega ^ 4) := by
      linear_combination omega_sum_expand
    rw [hrw, norm_neg, norm_pow, h1]
    norm_num

end Characters5
end Brockian

