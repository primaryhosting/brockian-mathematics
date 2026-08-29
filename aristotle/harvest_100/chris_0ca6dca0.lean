/-
# Twist Partial Sum Norm Le
Category: Characters
Target: Brockian.Characters5.twistPartialSum_norm_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-- The additive character `e` on `ZMod 5` given by `x ↦ ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

/-- Partial sums of the zero-mean twist. -/
noncomputable def twistPartialSum (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, e ((n : ZMod 5))

lemma omega_isPrimitiveRoot : IsPrimitiveRoot omega 5 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

lemma omega_pow_five : omega ^ 5 = 1 := omega_isPrimitiveRoot.pow_eq_one

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  have h1 : omega ^ 1 = 1 := by simpa using h
  have := omega_isPrimitiveRoot.dvd_of_pow_eq_one 1 h1
  omega

lemma norm_omega : ‖omega‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one omega_pow_five (by norm_num)

lemma norm_omega_pow (k : ℕ) : ‖omega ^ k‖ = 1 := by
  rw [norm_pow, norm_omega, one_pow]

/-- `e` at a natural number residue is just a power of `ω`. -/
lemma e_natCast (n : ℕ) : e ((n : ZMod 5)) = omega ^ n := by
  have hval : ((n : ZMod 5)).val = n % 5 := ZMod.val_natCast 5 n
  calc e ((n : ZMod 5)) = omega ^ (n % 5) := by rw [e, hval]
    _ = omega ^ n := by
        conv_rhs => rw [← Nat.div_add_mod n 5]
        rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma twistPartialSum_eq_geom (N : ℕ) :
    twistPartialSum N = ∑ n ∈ Finset.range N, omega ^ n := by
  refine Finset.sum_congr rfl ?_
  intro n _
  exact e_natCast n

/-- The full period sum vanishes (orthogonality / zero mean). -/
lemma sum_omega_pow : ∑ n ∈ Finset.range 5, omega ^ n = 0 := by
  rw [geom_sum_eq omega_ne_one, omega_pow_five, sub_self, zero_div]

lemma twistPartialSum_eq_mod (N : ℕ) : twistPartialSum N = twistPartialSum (N % 5) := by
  rw [twistPartialSum_eq_geom, twistPartialSum_eq_geom,
    geom_sum_eq omega_ne_one, geom_sum_eq omega_ne_one]
  congr 2
  conv_lhs => rw [← Nat.div_add_mod N 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

/-- Bounded partial sums of the zero-mean twist: `‖∑_{n < N} e (n mod 5)‖ ≤ 2`. -/
theorem twistPartialSum_norm_le (N : ℕ) : ‖twistPartialSum N‖ ≤ 2 := by
  rw [twistPartialSum_eq_mod, twistPartialSum_eq_geom]
  have h5 : N % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hsum := sum_omega_pow
  have hfive : (1 : ℂ) + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
    simpa [Finset.sum_range_succ, add_assoc] using hsum
  interval_cases h : (N % 5)
  · simp
  · simp
  · -- 1 + ω
    have : ∑ n ∈ Finset.range 2, omega ^ n = 1 + omega := by
      simp [Finset.sum_range_succ]
    rw [this]
    calc ‖(1 : ℂ) + omega‖ ≤ ‖(1 : ℂ)‖ + ‖omega‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, norm_omega]; norm_num
  · -- 1 + ω + ω² = -(ω³ + ω⁴)
    have h3 : ∑ n ∈ Finset.range 3, omega ^ n = -(omega ^ 3 + omega ^ 4) := by
      have : ∑ n ∈ Finset.range 3, omega ^ n = 1 + omega + omega ^ 2 := by
        simp [Finset.sum_range_succ]
      rw [this]; linear_combination hfive
    rw [h3, norm_neg]
    calc ‖omega ^ 3 + omega ^ 4‖ ≤ ‖omega ^ 3‖ + ‖omega ^ 4‖ := norm_add_le _ _
      _ = 2 := by rw [norm_omega_pow, norm_omega_pow]; norm_num
  · -- 1 + ω + ω² + ω³ = -ω⁴
    have h4 : ∑ n ∈ Finset.range 4, omega ^ n = -(omega ^ 4) := by
      have : ∑ n ∈ Finset.range 4, omega ^ n = 1 + omega + omega ^ 2 + omega ^ 3 := by
        simp [Finset.sum_range_succ]
      rw [this]; linear_combination hfive
    rw [h4, norm_neg, norm_omega_pow]
    norm_num

end Characters5
end Brockian

