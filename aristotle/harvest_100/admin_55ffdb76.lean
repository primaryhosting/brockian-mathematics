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

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

/-- The partial sums of the zero-mean twist. -/
noncomputable def twistPartialSum (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, e ((n : ZMod 5))

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma norm_omega : ‖omega‖ = 1 := by
  rw [omega, Complex.norm_exp]
  simp

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  rw [omega, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h3 : ((1 : ℂ) / 5 - n) * (2 * Real.pi * Complex.I) = 0 := by linear_combination hn
  have h4 : (1 : ℂ) / 5 - (n : ℂ) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h (by simp [hpi, Complex.I_ne_zero])
  have h5 : (5 * n : ℤ) = 1 := by
    have : ((5 * n : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by push_cast; linear_combination -5 * h4
    exact_mod_cast this
  omega

/-- The five fifth-roots of unity sum to zero. -/
lemma sum_omega_pow : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have hfac : (omega - 1) * (1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4) = 0 := by
    linear_combination omega_pow_five
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) omega_ne_one
  · exact h

lemma norm_omega_pow (k : ℕ) : ‖omega ^ k‖ = 1 := by
  rw [norm_pow, norm_omega, one_pow]

lemma e_natCast (n : ℕ) : e ((n : ZMod 5)) = omega ^ n := by
  rw [e, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma twistPartialSum_eq (N : ℕ) : twistPartialSum N = ∑ n ∈ Finset.range N, omega ^ n := by
  refine Finset.sum_congr rfl ?_
  intro n _
  exact e_natCast n

/-- Period-5 step. -/
lemma twistPartialSum_add_five (N : ℕ) : twistPartialSum (N + 5) = twistPartialSum N := by
  rw [twistPartialSum_eq, twistPartialSum_eq]
  rw [show N + 5 = N + 1 + 1 + 1 + 1 + 1 by ring]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have h : omega ^ N * (1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4) = 0 := by
    rw [sum_omega_pow, mul_zero]
  linear_combination h

lemma twistPartialSum_mod (N : ℕ) : twistPartialSum N = twistPartialSum (N % 5) := by
  have key : ∀ q r : ℕ, twistPartialSum (5 * q + r) = twistPartialSum r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ k ih =>
        intro r
        have : 5 * (k + 1) + r = (5 * k + r) + 5 := by ring
        rw [this, twistPartialSum_add_five, ih]
  conv_lhs => rw [← Nat.div_add_mod N 5]
  exact key (N / 5) (N % 5)

theorem twistPartialSum_norm_le (N : ℕ) : ‖twistPartialSum N‖ ≤ 2 := by
  rw [twistPartialSum_mod]
  have hr : N % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hsum := sum_omega_pow
  interval_cases h : (N % 5) <;>
    rw [twistPartialSum_eq] <;>
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero, pow_one,
      zero_add]
  · simp
  · rw [norm_one]; norm_num
  · calc ‖(1 : ℂ) + omega‖ ≤ ‖(1 : ℂ)‖ + ‖omega‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, norm_omega]; norm_num
  · have : (1 : ℂ) + omega + omega ^ 2 = -(omega ^ 3 + omega ^ 4) := by linear_combination hsum
    rw [this, norm_neg]
    calc ‖omega ^ 3 + omega ^ 4‖ ≤ ‖omega ^ 3‖ + ‖omega ^ 4‖ := norm_add_le _ _
      _ = 2 := by rw [norm_omega_pow, norm_omega_pow]; norm_num
  · have : (1 : ℂ) + omega + omega ^ 2 + omega ^ 3 = -(omega ^ 4) := by linear_combination hsum
    rw [this, norm_neg, norm_omega_pow]
    norm_num

end Characters5
end Brockian

