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

theorem exists_cycle_gap_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 3 ≤ n ∧ cycleGapFormula n < ε := by
  have h := cycleGapFormula_tendsto_zero
  have hev : ∀ᶠ n : ℕ in atTop, cycleGapFormula n < ε := by
    have := h (Iio_mem_nhds hε)
    simpa [Set.preimage] using this
  obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 3)).exists
  exact ⟨N, hN.2, hN.1⟩

/-- (b) **NEGATIVE / OBSTRUCTION RESULT.** There is no uniform positive lower
bound for the spectral gaps of the ordinary cycle graphs: no `ε > 0` satisfies
`ε ≤ cycleGapFormula n` for all `n ≥ 3`.

Consequently any construction aiming at a uniform spectral gap cannot be based
on plain cycles; a genuinely expanding (or otherwise modified) family is
required. -/
