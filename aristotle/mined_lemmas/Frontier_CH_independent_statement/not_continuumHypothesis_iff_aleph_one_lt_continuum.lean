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

theorem not_continuumHypothesis_iff_aleph_one_lt_continuum :
    ¬ ContinuumHypothesis ↔ (ℵ₁ : Cardinal.{0}) < 𝔠 := by
  rw [continuumHypothesis_iff_aleph_one_eq_continuum]
  exact ⟨fun h => lt_of_le_of_ne aleph_one_le_continuum h,
    fun h hEq => absurd hEq h.ne⟩

/-! ## Part 2: independence, model-theoretically

Since `Mathlib` has no proof calculus for first-order logic, we use the semantic
notion of consequence `T ⊨ᵇ φ`; by Gödel's completeness theorem this coincides with
provability from `T` in first-order logic.

`IndependentOf T φ` says that neither `φ` nor its negation is a consequence of `T`. -/

/-- A sentence `φ` is *independent* of a theory `T` when neither `φ` nor `¬ φ` is a
semantic consequence of `T` (equivalently, by Gödel completeness, when neither is
provable from `T`). -/
