/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

The Erdős discrepancy problem, solved by Terence Tao (2015), asserts that every
`±1`-valued sequence `f : ℕ → ℤ` has *unbounded* discrepancy along homogeneous
arithmetic progressions: for every bound `C` there are `d, n ≥ 1` with

  `|f d + f (2 d) + ⋯ + f (n d)| > C`.

This file formalises the statement (`Frontier.ErdosDiscrepancyProblem`) and proves
unconditionally the base case `C = 1`, in sharp form:

* `Frontier.erdos_discrepancy` : every `±1` sequence admits a homogeneous
  progression with `n * d ≤ 12` on which the partial sum has absolute value `> 1`;
* `Frontier.erdos_discrepancy_sharp` : the bound `12` cannot be lowered to `11`,
  witnessed by an explicit sequence of discrepancy `1` on all progressions inside
  `{1, …, 11}`.

It also contains a Lean-checked reduction: the infinite statement is equivalent to
its finite, uniform form `Frontier.FiniteEDP` (`erdosDiscrepancyProblem_of_finite`
and `finite_of_erdosDiscrepancyProblem`, the latter by compactness of the space of
`±1` sequences). The base case above is exactly `Frontier.FiniteEDP 1 12`.
-/

namespace Frontier

/-- The partial sum of `f` along the homogeneous arithmetic progression of common
difference `d`, taken over the first `n` terms: `f d + f (2 d) + ⋯ + f (n d)`. -/

theorem finiteEDP_one : FiniteEDP 1 12 := fun f hf => erdos_discrepancy f hf

