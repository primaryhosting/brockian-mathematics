/-!
# Twist Partial Sum Norm Le
Category: Characters
Target: Brockian.Characters5.twistPartialSum_norm_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The nontrivial additive character `e` on `ZMod 5` sending `x` to `ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using h

lemma omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

lemma omega_ne_one : omega ≠ 1 := isPrimitiveRoot_omega.ne_one (by norm_num)

lemma norm_omega : ‖omega‖ = 1 := by
  simp [omega, Complex.norm_exp]

lemma norm_e (x : ZMod 5) : ‖e x‖ = 1 := by
  simp [e, norm_pow, norm_omega]

/-- `e` on the natural number `n` is just `ω ^ n`, since `ω ^ 5 = 1`. -/
lemma e_natCast (n : ℕ) : e ((n : ZMod 5)) = omega ^ n := by
  rw [e, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

/-- The zero-mean (orthogonality) identity: the five fifth-roots of unity sum to zero. -/
lemma sum_omega_pow :
    omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h := isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)
  simp [Finset.sum_range_succ] at h
  linear_combination h

/-- Partial sums of the zero-mean twist. -/
noncomputable def twistPartialSum (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, e ((n : ZMod 5))

lemma twistPartialSum_eq_geom (N : ℕ) :
    twistPartialSum N = ∑ n ∈ Finset.range N, omega ^ n := by
  refine Finset.sum_congr rfl ?_
  intro n _
  exact e_natCast n

/-- Period-5 step: the twist partial sums are periodic with period 5. -/
lemma twistPartialSum_add_five (N : ℕ) : twistPartialSum (N + 5) = twistPartialSum N := by
  simp only [twistPartialSum_eq_geom]
  rw [show N + 5 = N + 1 + 1 + 1 + 1 + 1 by ring]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have h : omega ^ N * (omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4) = 0 := by
    rw [sum_omega_pow, mul_zero]
  ring_nf
  ring_nf at h
  linear_combination h

/-- Reduction to the residue of `N` modulo 5. -/
lemma twistPartialSum_mod (N : ℕ) : twistPartialSum N = twistPartialSum (N % 5) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 5 with hN | hN
    · rw [Nat.mod_eq_of_lt hN]
    · have hsub : N - 5 + 5 = N := by omega
      have h1 : twistPartialSum N = twistPartialSum (N - 5) := by
        rw [← hsub, twistPartialSum_add_five]
      have h2 : twistPartialSum (N - 5) = twistPartialSum ((N - 5) % 5) :=
        ih (N - 5) (by omega)
      have h3 : (N - 5) % 5 = N % 5 := by omega
      rw [h1, h2, h3]

lemma twistPartialSum_zero : twistPartialSum 0 = 0 := by
  simp [twistPartialSum]

lemma twistPartialSum_one : twistPartialSum 1 = 1 := by
  simp [twistPartialSum_eq_geom]

lemma twistPartialSum_two : twistPartialSum 2 = 1 + omega := by
  simp [twistPartialSum_eq_geom, Finset.sum_range_succ]

lemma twistPartialSum_three : twistPartialSum 3 = -(omega ^ 3 + omega ^ 4) := by
  have h := sum_omega_pow
  simp only [twistPartialSum_eq_geom, Finset.sum_range_succ, Finset.sum_range_zero]
  linear_combination h

lemma twistPartialSum_four : twistPartialSum 4 = -(omega ^ 4) := by
  have h := sum_omega_pow
  simp only [twistPartialSum_eq_geom, Finset.sum_range_succ, Finset.sum_range_zero]
  linear_combination h

/-- Bounded partial sums of the zero-mean twist: `‖∑_{n < N} e (n mod 5)‖ ≤ 2` for every `N`. -/
theorem twistPartialSum_norm_le (N : ℕ) : ‖twistPartialSum N‖ ≤ 2 := by
  rw [twistPartialSum_mod]
  have hlt : N % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (N % 5)
  · rw [twistPartialSum_zero]; norm_num
  · rw [twistPartialSum_one]; norm_num
  · rw [twistPartialSum_two]
    calc ‖(1 : ℂ) + omega‖ ≤ ‖(1 : ℂ)‖ + ‖omega‖ := norm_add_le _ _
      _ = 2 := by rw [norm_omega]; norm_num
  · rw [twistPartialSum_three]
    calc ‖-(omega ^ 3 + omega ^ 4)‖ = ‖omega ^ 3 + omega ^ 4‖ := norm_neg _
      _ ≤ ‖omega ^ 3‖ + ‖omega ^ 4‖ := norm_add_le _ _
      _ = 2 := by rw [norm_pow, norm_pow, norm_omega]; norm_num
  · rw [twistPartialSum_four, norm_neg, norm_pow, norm_omega]
    norm_num

end Characters5
end Brockian

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

