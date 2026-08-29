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
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` sending `x` to `ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

theorem omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

/-- `ω` has unit norm. -/
theorem norm_omega : ‖omega‖ = 1 := by
  simp [omega, Complex.norm_exp]

theorem norm_e (x : ZMod 5) : ‖e x‖ = 1 := by
  simp [e, norm_pow, norm_omega]

/-- The five fifth-roots of unity sum to zero. -/
theorem sum_omega_pow : ∑ i ∈ Finset.range 5, omega ^ i = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

/-- On natural-number arguments the character is just a power of `ω`. -/
theorem e_natCast (n : ℕ) : e ((n : ZMod 5)) = omega ^ n := by
  have hval : ((n : ZMod 5)).val = n % 5 := ZMod.val_natCast (n := 5) n
  calc e ((n : ZMod 5)) = omega ^ (n % 5) := by rw [e, hval]
    _ = (omega ^ 5) ^ (n / 5) * omega ^ (n % 5) := by rw [omega_pow_five, one_pow, one_mul]
    _ = omega ^ (5 * (n / 5) + n % 5) := by rw [pow_add, pow_mul]
    _ = omega ^ n := by rw [Nat.div_add_mod]

/-- Partial sums of the zero-mean twist. -/
noncomputable def twistPartialSum (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, e ((n : ZMod 5))

theorem twistPartialSum_eq (N : ℕ) : twistPartialSum N = ∑ n ∈ Finset.range N, omega ^ n := by
  refine Finset.sum_congr rfl ?_
  intro n _
  exact e_natCast n

/-- The partial sums are periodic with period `5`. -/
theorem twistPartialSum_period (N : ℕ) : twistPartialSum (N + 5) = twistPartialSum N := by
  simp only [twistPartialSum_eq]
  have hsplit : ∑ n ∈ Finset.range (N + 5), omega ^ n
      = (∑ n ∈ Finset.range N, omega ^ n) + ∑ j ∈ Finset.range 5, omega ^ (N + j) := by
    rw [Finset.sum_range_add]
  rw [hsplit]
  have : ∑ j ∈ Finset.range 5, omega ^ (N + j)
      = omega ^ N * ∑ j ∈ Finset.range 5, omega ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
  rw [this, sum_omega_pow, mul_zero, add_zero]

theorem twistPartialSum_mod (N : ℕ) : twistPartialSum N = twistPartialSum (N % 5) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 5 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 5 := ⟨N - 5, by omega⟩
      rw [twistPartialSum_period, ih M (by omega), Nat.add_mod_right]

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
theorem twistPartialSum_norm_le (N : ℕ) : ‖twistPartialSum N‖ ≤ 2 := by
  rw [twistPartialSum_mod N]
  exact twistPartialSum_norm_le_small (N % 5) (Nat.mod_lt _ (by norm_num))

end Brockian.Characters5

