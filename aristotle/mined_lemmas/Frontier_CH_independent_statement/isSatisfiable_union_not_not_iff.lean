import Mathlib

/-!
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Part 1: the Continuum Hypothesis inside Lean's own set theory
-/

open Cardinal

/-- The Continuum Hypothesis, phrased about sets of real numbers:
every infinite set of reals is either countable or of the cardinality of the continuum. -/

theorem isSatisfiable_union_not_not_iff (T : L.Theory) (σ : L.Sentence) :
    (T ∪ {σ.not.not}).IsSatisfiable ↔ (T ∪ {σ}).IsSatisfiable := by
  constructor
  · rintro ⟨M⟩
    have hM : M.Carrier ⊨ T ∪ {σ.not.not} := M.is_model
    rw [Theory.model_union_iff, Theory.model_singleton_iff] at hM
    have h2 : M.Carrier ⊨ T ∪ {σ} := by
      rw [Theory.model_union_iff, Theory.model_singleton_iff]
      exact ⟨hM.1, by simpa [Sentence.realize_not] using hM.2⟩
    exact ⟨⟨M.Carrier⟩⟩
  · rintro ⟨M⟩
    have hM : M.Carrier ⊨ T ∪ {σ} := M.is_model
    rw [Theory.model_union_iff, Theory.model_singleton_iff] at hM
    have h2 : M.Carrier ⊨ T ∪ {σ.not.not} := by
      rw [Theory.model_union_iff, Theory.model_singleton_iff]
      exact ⟨hM.1, by simpa [Sentence.realize_not] using hM.2⟩
    exact ⟨⟨M.Carrier⟩⟩

/-- **Reduction of independence to two consistency statements.** A sentence is independent of a
theory exactly when the theory together with the sentence, and the theory together with its
negation, are both satisfiable (equivalently, by Gödel completeness, both consistent). -/
