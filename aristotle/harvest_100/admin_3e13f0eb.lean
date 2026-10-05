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

/-- The primitive fifth root of unity `ω = e^{2πi/5}`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  have : (5 : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I := by
    ring
  push_cast
  rw [this, Complex.exp_two_pi_mul_I]

@[simp] lemma norm_omega : ‖omega‖ = 1 := by
  rw [omega, Complex.norm_exp]
  norm_num

lemma omega_ne_one : omega ≠ 1 := by
  rw [omega]
  intro hone
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hone
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi, Complex.I_ne_zero] at hn
  have hn5 : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

lemma sum_omega_pow : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have hfac : (omega - 1) * (1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4)
      = omega ^ 5 - 1 := by ring
  rw [omega_pow_five, sub_self] at hfac
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) omega_ne_one
  · exact h

/-- Partial sums of the zero-mean twist. -/
noncomputable def twistPartialSum (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, e ((n : ZMod 5))

lemma e_natCast (n : ℕ) : e ((n : ZMod 5)) = omega ^ n := by
  rw [e, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma twistPartialSum_eq (N : ℕ) : twistPartialSum N = ∑ n ∈ Finset.range N, omega ^ n := by
  simp [twistPartialSum, e_natCast]

lemma twistPartialSum_period (N : ℕ) : twistPartialSum (N + 5) = twistPartialSum N := by
  simp only [twistPartialSum_eq]
  rw [show N + 5 = N + 1 + 1 + 1 + 1 + 1 by ring]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have h := sum_omega_pow
  have : omega ^ N * (1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4) = 0 := by
    rw [h, mul_zero]
  linear_combination this

theorem twistPartialSum_norm_le (N : ℕ) : ‖twistPartialSum N‖ ≤ 2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 5 with hN | hN
    · interval_cases N
      · simp [twistPartialSum]
      · simp [twistPartialSum_eq]
      · rw [twistPartialSum_eq]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        calc ‖(0 : ℂ) + omega ^ 0 + omega ^ 1‖ ≤ ‖(0 : ℂ) + omega ^ 0‖ + ‖omega ^ 1‖ :=
              norm_add_le _ _
          _ ≤ 2 := by simp; norm_num
      · rw [twistPartialSum_eq]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_zero]
        have hrw : (0 : ℂ) + omega ^ 0 + omega ^ 1 + omega ^ 2 = -(omega ^ 3 + omega ^ 4) := by
          linear_combination sum_omega_pow
        rw [hrw, norm_neg]
        calc ‖omega ^ 3 + omega ^ 4‖ ≤ ‖omega ^ 3‖ + ‖omega ^ 4‖ := norm_add_le _ _
          _ ≤ 2 := by simp [norm_pow, norm_omega]; norm_num
      · rw [twistPartialSum_eq]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_succ, Finset.sum_range_zero]
        have hrw : (0 : ℂ) + omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 = -(omega ^ 4) := by
          linear_combination sum_omega_pow
        rw [hrw, norm_neg, norm_pow, norm_omega]
        norm_num
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 5 := ⟨N - 5, by omega⟩
      rw [twistPartialSum_period]
      exact ih M (by omega)

end Brockian.Characters5

#print axioms Brockian.Characters5.twistPartialSum_norm_le

