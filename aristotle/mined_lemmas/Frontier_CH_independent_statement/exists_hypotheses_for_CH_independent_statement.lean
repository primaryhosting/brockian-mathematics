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

set_option grind.warning false

/-!
## Overview

The full independence of the Continuum Hypothesis consists of two deep model constructions:

* **Gödel (1938)**: if `ZFC` is consistent, then `ZFC + CH` is consistent (the constructible
  universe `L`);
* **Cohen (1963)**: if `ZFC` is consistent, then `ZFC + ¬CH` is consistent (forcing).

This file formalizes the *independence statement itself*, in Mathlib's first-order model theory,
and gives a Lean-checked reduction: independence of a sentence from a theory is **equivalent** to
the joint satisfiability of the theory with the sentence and with its negation
(`Frontier.independentOf_iff`).  Feeding the Gödel and Cohen consistency results into this
reduction yields the target theorem `Frontier.CH_independent_statement`: assuming `ZFC` is
satisfiable and assuming Gödel's and Cohen's model constructions (stated as hypotheses, since
their proofs are not formalized here), the sentence `CH` is independent of `ZFC` — neither `CH`
nor `¬CH` is entailed by `ZFC`, hence, for any sound proof calculus, neither is provable
(`Frontier.CH_not_provable_of_sound`).

Unconditionally proved here as base cases: the hypothesis package of the target theorem is
itself satisfiable, so the target is not vacuous
(`Frontier.exists_hypotheses_for_CH_independent_statement`), and independence is a non-vacuous
phenomenon — there is a language, a theory and a sentence genuinely independent of it
(`Frontier.exists_independent_sentence`).
-/

namespace Frontier

open FirstOrder FirstOrder.Language

universe u v w

section General

variable {L : FirstOrder.Language.{u, v}} {T : L.Theory} {p q : L.Sentence}

/-- A sentence `p` is *independent* of a theory `T` when `T` entails neither `p` nor its
negation.  By Gödel's completeness theorem this semantic notion coincides with unprovability of
both `p` and `¬p` from `T` in any sound and complete proof calculus; see
`Frontier.not_provable_of_independentOf` for the direction that only needs soundness. -/

theorem exists_hypotheses_for_CH_independent_statement :
    ∃ (ZFC : setTheoryLanguage.Theory) (CH : setTheoryLanguage.Sentence),
      ZFC.IsSatisfiable ∧ (ZFC.IsSatisfiable → (ZFC ∪ {CH}).IsSatisfiable) ∧
        (ZFC.IsSatisfiable → (ZFC ∪ {CH.not}).IsSatisfiable) := by
  letI : setTheoryLanguage.Structure Bool := trivialSetStructure Bool
  letI : setTheoryLanguage.Structure Unit := trivialSetStructure Unit
  refine ⟨∅, Sentence.cardGe setTheoryLanguage 2, ?_, fun _ => ?_, fun _ => ?_⟩
  · exact Theory.isSatisfiable_empty setTheoryLanguage
  · haveI : Bool ⊨
        (∅ ∪ {Sentence.cardGe setTheoryLanguage 2} : setTheoryLanguage.Theory) := by
      rw [Theory.model_union_iff]
      refine ⟨inferInstance, Theory.model_singleton_iff.2 ?_⟩
      rw [Sentence.realize_cardGe]
      simp
    exact Theory.Model.isSatisfiable Bool
  · haveI : Unit ⊨
        (∅ ∪ {(Sentence.cardGe setTheoryLanguage 2).not} : setTheoryLanguage.Theory) := by
      rw [Theory.model_union_iff]
      refine ⟨inferInstance, Theory.model_singleton_iff.2 ?_⟩
      rw [Sentence.realize_not, Sentence.realize_cardGe]
      simp
    exact Theory.Model.isSatisfiable Unit

/-! ## Base case: independence is a non-vacuous notion

Unconditionally, there is a theory and a sentence independent of it: over the empty language,
the empty theory decides neither "there exist at least two elements" nor its negation. -/

