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

theorem cos_mode_le_cos_first (n : ℕ) (hn : 3 ≤ n) (k : Fin n) (hk : (k : ℕ) ≠ 0) :
    Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)) ≤ Real.cos (2 * Real.pi / (n : ℝ)) := by
  set a : ℝ := 2 * Real.pi / (n : ℝ) with ha
  set θ : ℝ := 2 * Real.pi * (k : ℝ) / (n : ℝ) with hθ
  have ha0 : 0 < a := angle_pos hn
  have hlb : a ≤ θ := angle_lower hn k hk
  have hub : θ ≤ 2 * Real.pi - a := angle_upper hn k
  rcases le_or_gt θ Real.pi with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi ha0.le h hlb
  · have hsym : Real.cos θ = Real.cos (2 * Real.pi - θ) := by
      rw [Real.cos_two_pi_sub]
    rw [hsym]
    exact Real.cos_le_cos_of_nonneg_of_le_pi ha0.le (by linarith) (by linarith)

/-- **Minimality theorem.** The gap formula lower-bounds every nontrivial
eigenvalue of the cycle. -/
