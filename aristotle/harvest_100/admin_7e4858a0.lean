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
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

local notation "ω" => omega

/-- The additive character `e : ZMod 5 → ℂ`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := ω ^ x.val

/-- `ω` is a primitive fifth root of unity. -/
theorem isPrimitiveRoot_omega : IsPrimitiveRoot ω 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using h

theorem omega_pow_five : ω ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

theorem norm_omega : ‖ω‖ = 1 := by
  have h := omega_pow_five
  have : ‖ω‖ ^ 5 = 1 := by
    rw [← norm_pow, h, norm_one]
  nlinarith [norm_nonneg ω, sq_nonneg (‖ω‖ - 1), sq_nonneg (‖ω‖ + 1),
    sq_nonneg (‖ω‖ ^ 2 - 1)]

theorem norm_e (x : ZMod 5) : ‖e x‖ = 1 := by
  simp [e, norm_pow, norm_omega]

/-- The five fifth-roots of unity sum to zero (orthogonality / zero mean). -/
theorem sum_omega_pow : ∑ i ∈ Finset.range 5, ω ^ i = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

/-- Partial sums of the zero-mean twist. -/
noncomputable def twistPartialSum (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, e ((n : ZMod 5))

theorem e_natCast (n : ℕ) : e ((n : ZMod 5)) = ω ^ n := by
  have hval : ((n : ZMod 5)).val = n % 5 := by
    simp [ZMod.val_natCast]
  calc e ((n : ZMod 5)) = ω ^ (n % 5) := by rw [e, hval]
    _ = (ω ^ 5) ^ (n / 5) * ω ^ (n % 5) := by rw [omega_pow_five, one_pow, one_mul]
    _ = ω ^ (5 * (n / 5) + n % 5) := by rw [pow_add, pow_mul]
    _ = ω ^ n := by rw [Nat.div_add_mod]

theorem twistPartialSum_eq_geom (N : ℕ) :
    twistPartialSum N = ∑ n ∈ Finset.range N, ω ^ n := by
  simp [twistPartialSum, e_natCast]

/-- Period-5 step. -/
theorem twistPartialSum_add_five (N : ℕ) : twistPartialSum (N + 5) = twistPartialSum N := by
  rw [twistPartialSum_eq_geom, twistPartialSum_eq_geom, Finset.sum_range_add]
  have : ∑ x ∈ Finset.range 5, ω ^ (N + x) = ω ^ N * ∑ x ∈ Finset.range 5, ω ^ x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [pow_add]
  rw [this, sum_omega_pow, mul_zero, add_zero]

theorem twistPartialSum_mod (N : ℕ) : twistPartialSum N = twistPartialSum (N % 5) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 5 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have hN : N = (N - 5) + 5 := by omega
      have hmod : (N - 5) % 5 = N % 5 := by omega
      have key : twistPartialSum N = twistPartialSum (N - 5) := by
        conv_lhs => rw [hN]
        rw [twistPartialSum_add_five]
      rw [key, ih (N - 5) (by omega), hmod]

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
theorem twistPartialSum_norm_le (N : ℕ) : ‖twistPartialSum N‖ ≤ 2 := by
  rw [twistPartialSum_mod N]
  exact twistPartialSum_norm_le_of_lt_five _ (Nat.mod_lt _ (by norm_num))

end Brockian.Characters5

