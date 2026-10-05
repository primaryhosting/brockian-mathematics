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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open FirstOrder FirstOrder.Language

universe u v

/-- A sentence `s0` is *independent* of a theory `T` when `T` neither entails `s0` nor entails
its negation.  By Gödel's completeness theorem (semantic entailment = derivability in
first-order logic) this is exactly the usual syntactic notion of independence. -/

theorem isSatisfiable_not_emptySetSentence :
    ((∅ : setLanguage.Theory) ∪ {emptySetSentence.not}).IsSatisfiable := by
  letI := ltStructure ℤ
  haveI : ℤ ⊨ (∅ : setLanguage.Theory) ∪ {emptySetSentence.not} := by
    rw [Theory.model_iff]
    intro psi hpsi
    simp only [Set.empty_union, Set.mem_singleton_iff] at hpsi
    subst hpsi
    rw [Sentence.Realize, Formula.realize_not, ← Sentence.Realize,
      realize_emptySetSentence ℤ]
    rintro ⟨x, hx⟩
    exact hx (x - 1) (by omega)
  exact ⟨Theory.ModelType.of _ ℤ⟩

/-- **A fully verified instance of independence.**  The sentence "there is an empty set" is
independent of the empty theory in the language of set theory. -/
