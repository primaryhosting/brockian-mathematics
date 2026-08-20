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
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma omega_ne_one : omega ≠ 1 := by
  rw [omega, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI := Complex.I_ne_zero
  field_simp at hn
  have hn' : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

lemma norm_omega : ‖omega‖ = 1 := by
  rw [omega, Complex.norm_exp]
  norm_num [Complex.div_re, Complex.mul_re]

lemma sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  rw [geom_sum_eq omega_ne_one, omega_pow_five]
  simp

/-- The expanded form of the zero-mean identity. -/
lemma omega_sum_expand : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h := sum_omega_pow
  simp [Finset.sum_range_succ] at h
  linear_combination h

lemma norm_e (x : ZMod 5) : ‖e x‖ = 1 := by
  rw [e, norm_pow, norm_omega, one_pow]

/-- The partial sums of the zero-mean twist. -/
noncomputable def twistPartialSum (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, e ((n : ZMod 5))

lemma e_natCast (n : ℕ) : e ((n : ZMod 5)) = omega ^ n := by
  rw [e, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma twistPartialSum_eq (N : ℕ) : twistPartialSum N = ∑ n ∈ Finset.range N, omega ^ n := by
  simp [twistPartialSum, e_natCast]

lemma twistPartialSum_add_five (N : ℕ) : twistPartialSum (N + 5) = twistPartialSum N := by
  rw [twistPartialSum_eq, twistPartialSum_eq]
  simp only [show N + 5 = N + 1 + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ]
  linear_combination omega ^ N * omega_sum_expand

lemma twistPartialSum_mod (N : ℕ) : twistPartialSum N = twistPartialSum (N % 5) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 5 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 5 := ⟨N - 5, by omega⟩
      rw [twistPartialSum_add_five, ih M (by omega), Nat.add_mod_right]

/-- Bounded partial sums of the zero-mean twist on `ZMod 5`. -/
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

