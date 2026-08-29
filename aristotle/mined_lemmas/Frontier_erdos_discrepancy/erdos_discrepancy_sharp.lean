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

theorem erdos_discrepancy_sharp :
    ∃ f : ℕ → ℤ, IsPMOne f ∧
      ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ 11 → |hapSum f d n| ≤ 1 := by
  refine ⟨sharpSeq, sharpSeq_isPMOne, ?_⟩
  have key : ∀ d ∈ Finset.Icc 1 11, ∀ n ∈ Finset.Icc 1 11,
      n * d ≤ 11 → |hapSum sharpSeq d n| ≤ 1 := by decide
  intro d n hd hn hnd
  have hdn : d ≤ n * d := Nat.le_mul_of_pos_left d hn
  have hnd' : n ≤ n * d := Nat.le_mul_of_pos_right n hd
  exact key d (Finset.mem_Icc.mpr ⟨hd, by omega⟩) n (Finset.mem_Icc.mpr ⟨hn, by omega⟩) hnd

/-!
## A Lean-checked reduction: the finite form is equivalent to the infinite form

`FiniteEDP C N` says that *every* `±1` sequence already exhibits discrepancy `> C`
inside the window `n * d ≤ N`. Trivially the finite form implies the infinite one;
the converse is a compactness argument, carried out below.
-/

/-- The finite (uniform, quantitative) form of the Erdős discrepancy problem:
every `±1` sequence has discrepancy exceeding `C` on some homogeneous progression
whose largest element is at most `N`. -/
