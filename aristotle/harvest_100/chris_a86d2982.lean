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
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, `e x = ω^{x.val}`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

/-- Partial sums of the zero-mean twist. -/
noncomputable def twistPartialSum (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, e ((n : ZMod 5))

lemma omega_pow_five : omega ^ 5 = 1 := by
  have : omega ^ 5 = Complex.exp (2 * Real.pi * Complex.I) := by
    rw [omega, ← Complex.exp_nat_mul]
    ring_nf
  rw [this, Complex.exp_two_pi_mul_I]

lemma norm_omega : ‖omega‖ = 1 := by
  rw [omega, Complex.norm_exp]
  norm_num

lemma omega_ne_one : omega ≠ 1 := by
  rw [omega, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp at hn
  have hz : ((1 : ℤ) : ℂ) = ((5 * n : ℤ) : ℂ) := by push_cast; linear_combination hn
  have hint : (1 : ℤ) = 5 * n := by exact_mod_cast hz
  omega

/-- The full period sum vanishes: `∑_{j<5} ω^j = 0`. -/
lemma sum_omega_pow : ∑ j ∈ Finset.range 5, omega ^ j = 0 := by
  have h := geom_sum_mul omega 5
  rw [omega_pow_five, sub_self] at h
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) omega_ne_one

/-- `e` evaluated at the residue of `n` is just `ω ^ n`. -/
lemma e_natCast (n : ℕ) : e ((n : ZMod 5)) = omega ^ n := by
  rw [e, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma twistPartialSum_eq (N : ℕ) : twistPartialSum N = ∑ n ∈ Finset.range N, omega ^ n := by
  simp [twistPartialSum, e_natCast]

lemma twistPartialSum_period (N : ℕ) : twistPartialSum (N + 5) = twistPartialSum N := by
  rw [twistPartialSum_eq, twistPartialSum_eq, Finset.sum_range_add]
  have : ∑ j ∈ Finset.range 5, omega ^ (N + j) = omega ^ N * ∑ j ∈ Finset.range 5, omega ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
  rw [this, sum_omega_pow, mul_zero, add_zero]

lemma twistPartialSum_mod (N : ℕ) : twistPartialSum N = twistPartialSum (N % 5) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 5 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 5 := ⟨N - 5, by omega⟩
      rw [twistPartialSum_period, ih M (by omega), Nat.add_mod_right]

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

