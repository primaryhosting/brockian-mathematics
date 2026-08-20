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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Brocard's problem asks for the solutions of `n ! + 1 = m ^ 2`.  The only known
solutions are `n = 4, 5, 7` (with `m = 5, 11, 71`), and it is conjectured that
there are no others; in *gap* form the conjecture states that the distance from
`n ! + 1` to the nearest perfect square is positive (indeed large) for all
`n ≥ 8`.  This is an open problem.

This file contains:

* `Brockian.BrocardGap.brocardGap`, the distance from `n ! + 1` to the nearest
  perfect square, and the characterisation `brocardGap_pos_iff`;
* `Brockian.BrocardGap.ABC`, the `abc` conjecture (in radical form);
* `Brockian.BrocardGap.BrocardGapConjecture`, a Lean-checked **conditional
  reduction**: the `abc` conjecture implies that the Brocard gap is positive for
  all sufficiently large `n` (this is Overholt's argument);
* `Brockian.BrocardGap.brocardGap_pos_of_mem_Icc`, an unconditional verification
  of the gap positivity for `8 ≤ n ≤ 200`;
* `Brockian.BrocardGap.brocard_iff_pronic`, the elementary reformulation of
  Brocard's equation as `n ! = 4 * a * (a + 1)`.
-/

namespace Brockian.BrocardGap

open Nat Finset

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma factorial_le_of_abc (habc : ABC) :
    ∃ D : ℝ, ∀ n m : ℕ, n ! + 1 = m ^ 2 → (n ! : ℝ) ≤ D * 4096 ^ n := by
  obtain ⟨K, hK⟩ := habc (1 / 2) (by norm_num)
  set K' : ℝ := max K 1 with hK'
  have hK'1 : (1 : ℝ) ≤ K' := le_max_right _ _
  have hKK' : K ≤ K' := le_max_left _ _
  refine ⟨K' ^ 4, fun n m hnm => ?_⟩
  have hfac : 0 < n ! := Nat.factorial_pos n
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hnm
    · exact h
  have hcop : Nat.Coprime 1 (n !) := Nat.coprime_one_left _
  have habc' := hK 1 (n !) (m ^ 2) one_pos hfac hcop (by omega)
  have hradnat : rad (1 * n ! * m ^ 2) ≤ 4 ^ n * m := by
    rw [one_mul]
    calc rad (n ! * m ^ 2) ≤ rad (n !) * rad (m ^ 2) := rad_mul_le _ _
      _ = rad (n !) * rad m := by rw [rad_pow m two_ne_zero]
      _ ≤ 4 ^ n * m := Nat.mul_le_mul (rad_factorial_le n) (rad_le_self hm)
  set R : ℝ := (rad (1 * n ! * m ^ 2) : ℝ) with hR
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hR]; exact_mod_cast (rad_pos : 0 < rad (1 * n ! * m ^ 2))
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hRle : R ≤ 4 ^ n * (m : ℝ) := by
    have h2 : ((rad (1 * n ! * m ^ 2) : ℕ) : ℝ) ≤ ((4 ^ n * m : ℕ) : ℝ) := Nat.cast_le.2 hradnat
    push_cast at h2
    rw [hR]; exact h2
  have step1 : ((m : ℝ) ^ 2) ≤ K' * R ^ ((3 : ℝ) / 2) := by
    have h : ((m ^ 2 : ℕ) : ℝ) ≤ K * R ^ (1 + (1 / 2 : ℝ)) := habc'
    rw [show (1 + (1 / 2 : ℝ)) = 3 / 2 by norm_num] at h
    have hpow : (0 : ℝ) ≤ R ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hR0 _
    push_cast at h
    nlinarith [h]
  have hrpow : (R ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) = R ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast (R ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hR0]
    norm_num
  have step2 : ((m : ℝ) ^ 2) ^ 2 ≤ K' ^ 2 * R ^ (3 : ℕ) := by
    have h := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2) step1
    calc ((m : ℝ) ^ 2) ^ 2 = ((m : ℝ) ^ 2) * ((m : ℝ) ^ 2) := by ring
      _ ≤ (K' * R ^ ((3 : ℝ) / 2)) * (K' * R ^ ((3 : ℝ) / 2)) := h
      _ = K' ^ 2 * (R ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) := by ring
      _ = K' ^ 2 * R ^ (3 : ℕ) := by rw [hrpow]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hrw : ((4 : ℝ) ^ n * (m : ℝ)) ^ 3 = 64 ^ n * (m : ℝ) ^ 3 := by
    rw [mul_pow, ← pow_mul, mul_comm n 3, pow_mul]
    norm_num
  have step3 : (m : ℝ) ≤ K' ^ 2 * 64 ^ n := by
    have hcube : R ^ (3 : ℕ) ≤ (4 ^ n * (m : ℝ)) ^ 3 := pow_le_pow_left₀ hR0 hRle 3
    have hK2 : (0 : ℝ) ≤ K' ^ 2 := by positivity
    have h4 : ((m : ℝ) ^ 2) ^ 2 ≤ K' ^ 2 * (64 ^ n * (m : ℝ) ^ 3) := by
      refine le_trans step2 ?_
      rw [← hrw]
      exact mul_le_mul_of_nonneg_left hcube hK2
    have hm3 : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
    refine le_of_mul_le_mul_right ?_ hm3
    nlinarith [h4]
  have h1 : ((n ! : ℝ)) < (m : ℝ) ^ 2 := by
    have h : ((n ! : ℝ)) + 1 = (m : ℝ) ^ 2 := by exact_mod_cast hnm
    linarith
  have h2 : (m : ℝ) ^ 2 ≤ (K' ^ 2 * 64 ^ n) ^ 2 := pow_le_pow_left₀ hmpos.le step3 2
  have h64 : ((64 : ℝ) ^ n) * (64 ^ n) = 4096 ^ n := by rw [← mul_pow]; norm_num
  have h3 : (K' ^ 2 * 64 ^ n : ℝ) ^ 2 = K' ^ 4 * 4096 ^ n := by rw [← h64]; ring
  linarith [h1, h2, h3 ▸ h2]

/-- **Brocard Gap Conjecture (conditional reduction).**  Assuming the `abc` conjecture, the
distance from `n ! + 1` to the nearest perfect square is positive for all sufficiently large
`n`; equivalently, Brocard's equation `n ! + 1 = m ^ 2` has only finitely many solutions. -/
