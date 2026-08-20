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

private lemma angle_le_pi (hn : 3 ≤ n) : 2 * Real.pi / (n : ℝ) ≤ Real.pi := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
    have : 2 ≤ n := by omega
    exact_mod_cast this
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have := Real.pi_pos
  rw [div_le_iff₀ hn0]
  nlinarith

end Angle

/-! ### Positivity of the nontrivial eigenvalues -/

/-- Every nonzero Fourier mode of the cycle has strictly positive eigenvalue. -/
