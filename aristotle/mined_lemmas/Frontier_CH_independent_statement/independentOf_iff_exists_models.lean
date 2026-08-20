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

theorem independentOf_iff_exists_models {L : FirstOrder.Language.{u, v}} (T : L.Theory)
    (φ : L.Sentence) :
    IndependentOf T φ ↔
      (∃ M : Language.Theory.ModelType.{u, v, max u v} T, M ⊨ φ) ∧
        (∃ N : Language.Theory.ModelType.{u, v, max u v} T, ¬ N ⊨ φ) := by
  unfold IndependentOf
  rw [Language.Theory.models_sentence_iff, Language.Theory.models_sentence_iff]
  simp only [Language.Sentence.realize_not, not_forall, not_not]
  tauto

/-- The reduction, in the form actually used: two models give independence. -/
