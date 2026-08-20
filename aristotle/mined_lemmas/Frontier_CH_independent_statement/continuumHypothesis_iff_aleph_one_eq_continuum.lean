/-
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Cardinal FirstOrder

namespace Frontier

/-! ## Part 1: the Continuum Hypothesis as a statement about cardinals

We first record the "external" form of CH — the statement, about the actual real
numbers, that every uncountable set of reals has the cardinality of the continuum —
and prove that it is equivalent to the usual cardinal arithmetic form `ℵ₁ = 𝔠`.
This is a genuine (and fully proved) Lean theorem; it is the base case of the
formalization. -/

/-- The Continuum Hypothesis, in the form: every uncountable set of real numbers has
cardinality the continuum. -/

theorem continuumHypothesis_iff_aleph_one_eq_continuum :
    ContinuumHypothesis ↔ (ℵ₁ : Cardinal.{0}) = 𝔠 := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ :=
      le_mk_iff_exists_set.1 (show (ℵ₁ : Cardinal.{0}) ≤ #ℝ by
        rw [mk_real]; exact aleph_one_le_continuum)
    have hnc : ¬ s.Countable := by
      rw [Cardinal.countable_iff_lt_aleph_one, hs]
      exact lt_irrefl _
    exact hs.symm.trans (h s hnc)
  · intro h s hs
    refine le_antisymm ?_ ?_
    · calc #s ≤ #ℝ := mk_set_le s
        _ = 𝔠 := mk_real
    · rw [Cardinal.countable_iff_lt_aleph_one, not_lt] at hs
      exact le_trans (le_of_eq h.symm) hs

/-- The negation of the Continuum Hypothesis is equivalent to `ℵ₁ < 𝔠`. -/
