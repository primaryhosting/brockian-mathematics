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

import Mathlib

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter UniqueFactorizationMonoid
open scoped Nat

namespace Brockian.BrocardProblem

/-- The `abc` conjecture, stated for natural numbers, using the radical
`UniqueFactorizationMonoid.radical` (the product of the distinct prime factors):
for every `ε > 0` there is a constant `K > 0` such that whenever `a + b = c` with
`a, b` positive and coprime, we have `c ≤ K * rad(a * b * c) ^ (1 + ε)`. -/

lemma factorial_le_of_abc (habc : ABCConjecture) :
    ∃ C : ℝ, 0 < C ∧ ∀ n ∈ brocardSet, (n ! : ℝ) ≤ C * 4096 ^ n := by
  obtain ⟨K, hK, h⟩ := habc (1 / 2) (by norm_num)
  refine ⟨K ^ 4, by positivity, ?_⟩
  rintro n ⟨m, hm⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have key := h 1 (n !) (m ^ 2) one_pos (Nat.factorial_pos n) (Nat.coprime_one_left _) (by omega)
  have hR : (Nat.cast (radical (1 * n ! * m ^ 2)) : ℝ) ≤ (4 : ℝ) ^ n * m := by
    have hrb := radical_brocard_le n hm0
    calc (Nat.cast (radical (1 * n ! * m ^ 2)) : ℝ) ≤ ((4 ^ n * m : ℕ) : ℝ) := by exact_mod_cast hrb
      _ = (4 : ℝ) ^ n * m := by push_cast; ring
  have hpos : (0 : ℝ) < (4 : ℝ) ^ n * m := by positivity
  have hstep : ((m : ℝ) ^ 2) ≤ K * ((4 : ℝ) ^ n * m) ^ (1 + (1 / 2 : ℝ)) := by
    have hmono := Real.rpow_le_rpow (by positivity) hR (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)
    have hcast2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
    rw [hcast2] at key
    calc ((m : ℝ) ^ 2)
        ≤ K * (Nat.cast (radical (1 * n ! * m ^ 2)) : ℝ) ^ (1 + (1 / 2 : ℝ)) := key
      _ ≤ K * ((4 : ℝ) ^ n * m) ^ (1 + (1 / 2 : ℝ)) := by nlinarith [hmono]
  have hx : ((4 : ℝ) ^ n * m) ^ (1 + (1 / 2 : ℝ)) = Real.sqrt (((4 : ℝ) ^ n * m) ^ 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((4 : ℝ) ^ n * m) 3, ← Real.rpow_mul hpos.le]
    norm_num
  rw [hx] at hstep
  have hsqrt2 : (Real.sqrt (((4 : ℝ) ^ n * m) ^ 3)) ^ 2 = ((4 : ℝ) ^ n * m) ^ 3 :=
    Real.sq_sqrt (by positivity)
  have hsq : ((m : ℝ) ^ 2) ^ 2 ≤ K ^ 2 * ((4 : ℝ) ^ n * m) ^ 3 := by
    nlinarith [hstep, Real.sqrt_nonneg (((4 : ℝ) ^ n * m) ^ 3), hsqrt2, sq_nonneg ((m : ℝ) ^ 2)]
  have e1 : ((4 : ℝ) ^ n) ^ 3 = 64 ^ n := by
    rw [← pow_mul, mul_comm n 3, pow_mul]; norm_num
  have hmle : (m : ℝ) ≤ K ^ 2 * 64 ^ n := by
    have h4 : ((4 : ℝ) ^ n * m) ^ 3 = 64 ^ n * (m : ℝ) ^ 3 := by rw [mul_pow, e1]
    rw [h4] at hsq
    have hm3 : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
    have hmul : (m : ℝ) * (m : ℝ) ^ 3 ≤ (K ^ 2 * 64 ^ n) * (m : ℝ) ^ 3 := by nlinarith [hsq]
    exact le_of_mul_le_mul_right hmul hm3
  have hcast : (n ! : ℝ) + 1 = (m : ℝ) ^ 2 := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hm
  have e2 : ((64 : ℝ) ^ n) ^ 2 = 4096 ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
  have hfin : (m : ℝ) ^ 2 ≤ K ^ 4 * 4096 ^ n := by
    have hsq2 : (m : ℝ) ^ 2 ≤ (K ^ 2 * 64 ^ n) ^ 2 := by nlinarith [hmle, hm0'.le]
    calc (m : ℝ) ^ 2 ≤ (K ^ 2 * 64 ^ n) ^ 2 := hsq2
      _ = K ^ 4 * 4096 ^ n := by rw [mul_pow, e2, ← pow_mul]
  linarith [hcast, hfin]

/-- Only finitely many `n` satisfy `n ! ≤ C * B ^ n`, since `n !` grows faster than any
geometric sequence. -/
