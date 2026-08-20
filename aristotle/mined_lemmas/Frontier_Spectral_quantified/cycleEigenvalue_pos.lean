import Frontier.Spectral.CycleGapObstruction

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

/-
# NEGATIVE / OBSTRUCTION RESULT: the cycle spectral gap vanishes

This module proves an **honest negative result** about the explicit family of
real Fourier eigenvalues of ordinary (unweighted, undirected) cycle graphs:

  `cycleEigenvalue n k = 2 - 2 * Real.cos (2 * π * k / n)`,  `k : Fin n`.

Contents:

* `cycleEigenvalue_zero`      : the eigenvalue at `k = 0` is `0`;
* `cycleEigenvalue_pos`       : all other eigenvalues are strictly positive;
* `cycleEigenvalue_gap_le`, `cycleEigenvalue_isLeast` :
    the *least positive* eigenvalue is exactly
    `cycleGapFormula n = 2 - 2 * cos (2 * π / n)` — a genuine minimality

theorem cycleEigenvalue_pos (n : ℕ) (hn : 3 ≤ n) (k : Fin n) (hk : (k : ℕ) ≠ 0) :
    0 < cycleEigenvalue n k := by
  set θ : ℝ := 2 * Real.pi * (k : ℝ) / (n : ℝ) with hθ
  have hlb : 0 < θ := lt_of_lt_of_le (angle_pos hn) (angle_lower hn k hk)
  have hub : θ < 2 * Real.pi := by
    have := angle_upper hn k
    have := angle_pos (n := n) hn
    linarith
  have hne : Real.cos θ ≠ 1 := by
    intro h
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hub).mp h
    linarith
  have hle : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have : Real.cos θ < 1 := lt_of_le_of_ne hle hne
  simp only [cycleEigenvalue, ← hθ]
  linarith

/-- Restatement of `cycleEigenvalue_pos` with the index compared to the zero
element of `Fin n` directly. -/
