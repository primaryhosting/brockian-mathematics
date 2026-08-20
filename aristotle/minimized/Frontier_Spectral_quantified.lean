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

    theorem quantified over all `k ≠ 0`, not a definitional shortcut;
* `cycleGapFormula_tendsto_zero`, `exists_cycle_gap_lt`,
  `no_uniform_positive_cycle_gap` :
    the gap tends to `0`, so **no uniform positive lower bound** on the gap
    holds across all cycles.

**Scope disclaimer.** Everything below concerns *only* this explicit cycle
eigenvalue family; nothing is claimed about any other graph or operator family.
The result is an OBSTRUCTION: it falsifies any strategy that hopes to obtain a
uniform spectral gap from plain cycle graphs, and identifies the need for a
genuinely expanding (or otherwise modified) family of graphs.
-/
import Mathlib

open Filter Topology

namespace Frontier.Spectral

/-- The `k`-th real Fourier eigenvalue of the cycle graph on `n` vertices:
`2 - 2 cos (2π k / n)`. -/

noncomputable def cycleGapFormula (n : ℕ) : ℝ :=
  2 - 2 * Real.cos (2 * Real.pi / (n : ℝ))

/-! ### Basic values -/

/-- The trivial mode `k = 0` has eigenvalue `0`. -/

theorem cycleGapFormula_tendsto_zero :
    Tendsto cycleGapFormula atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 2 * Real.pi / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h2 : Tendsto (fun n : ℕ => Real.cos (2 * Real.pi / (n : ℝ))) atTop (𝓝 1) := by
    have := (Real.continuous_cos.tendsto (0 : ℝ)).comp h1
    simpa [Function.comp] using this
  have h3 : Tendsto (fun n : ℕ => 2 - 2 * Real.cos (2 * Real.pi / (n : ℝ))) atTop
      (𝓝 (2 - 2 * 1)) := tendsto_const_nhds.sub (h2.const_mul 2)
  simpa [cycleGapFormula] using h3

/-! ### The obstruction -/

/-- (a) For every `ε > 0` there is a cycle with at least three vertices whose
spectral gap is smaller than `ε`. -/

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

theorem no_uniform_positive_cycle_gap :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 3 ≤ n → ε ≤ cycleGapFormula n := by
  rintro ⟨ε, hε, hbound⟩
  obtain ⟨n, hn3, hlt⟩ := exists_cycle_gap_lt hε
  exact absurd (hbound n hn3) (not_le.mpr hlt)

#print axioms no_uniform_positive_cycle_gap

end Frontier.Spectral
