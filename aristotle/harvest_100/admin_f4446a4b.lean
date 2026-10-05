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
def IndependentOf (T : L.Theory) (p : L.Sentence) : Prop :=
  ¬ T ⊨ᵇ p ∧ ¬ T ⊨ᵇ p.not

/-- Transporting satisfiability of `T ∪ {q}` to `T ∪ {p}` along an implication valid in all
structures. -/
theorem isSatisfiable_union_singleton_of_imp
    (himp : ∀ (M : Type (max u v)) [L.Structure M], M ⊨ q → M ⊨ p)
    (h : (T ∪ {q}).IsSatisfiable) : (T ∪ {p}).IsSatisfiable := by
  obtain ⟨M⟩ := h
  have hm := M.is_model
  rw [Theory.model_union_iff] at hm
  have hp : (M : Type (max u v)) ⊨ p := himp _ (Theory.model_singleton_iff.1 hm.2)
  haveI : (M : Type (max u v)) ⊨ T ∪ {p} :=
    Theory.model_union_iff.2 ⟨hm.1, Theory.model_singleton_iff.2 hp⟩
  exact Theory.Model.isSatisfiable (T := T ∪ {p}) (M : Type (max u v))

/-- If `T` together with `¬p` has a model, then `T` does not entail `p`. -/
theorem not_models_of_isSatisfiable_not (h : (T ∪ {p.not}).IsSatisfiable) : ¬ T ⊨ᵇ p := by
  rw [Theory.models_iff_not_satisfiable]
  exact not_not_intro h

/-- If `T` together with `p` has a model, then `T` does not entail `¬p`. -/
theorem not_models_not_of_isSatisfiable (h : (T ∪ {p}).IsSatisfiable) : ¬ T ⊨ᵇ p.not := by
  rw [Theory.models_iff_not_satisfiable]
  refine not_not_intro (isSatisfiable_union_singleton_of_imp ?_ h)
  intro M _ hM
  rw [Sentence.realize_not]
  exact fun hc => (Sentence.realize_not M).1 hc hM

/-- **Reduction of independence to consistency.**  A sentence is independent of a theory as soon
as the theory is consistent both with the sentence and with its negation. -/
theorem independentOf_of_isSatisfiable (h₁ : (T ∪ {p}).IsSatisfiable)
    (h₂ : (T ∪ {p.not}).IsSatisfiable) : IndependentOf T p :=
  ⟨not_models_of_isSatisfiable_not h₂, not_models_not_of_isSatisfiable h₁⟩

/-- **Independence is exactly two-sided consistency.** -/
theorem independentOf_iff :
    IndependentOf T p ↔ (T ∪ {p}).IsSatisfiable ∧ (T ∪ {p.not}).IsSatisfiable := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [Theory.models_iff_not_satisfiable, not_not] at h1 h2
    refine ⟨isSatisfiable_union_singleton_of_imp ?_ h2, h1⟩
    intro M _ hM
    by_contra hc
    exact (Sentence.realize_not M).1 hM ((Sentence.realize_not M).2 hc)
  · rintro ⟨h1, h2⟩
    exact independentOf_of_isSatisfiable h1 h2

/-- Independence rules out provability in *any* sound proof calculus. -/
theorem not_provable_of_independentOf
    {Provable : L.Theory → L.Sentence → Prop}
    (sound : ∀ (S : L.Theory) (q : L.Sentence), Provable S q → S ⊨ᵇ q)
    (h : IndependentOf T p) : ¬ Provable T p ∧ ¬ Provable T p.not := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun hp => h1 (sound _ _ hp), fun hp => h2 (sound _ _ hp)⟩

end General

/-! ## The language of set theory -/

/-- The first-order language of set theory: no function symbols, a single binary relation `∈`. -/
def setTheoryLanguage : FirstOrder.Language.{0, 0} where
  Functions := fun _ => Empty
  Relations := fun n => PLift (n = 2)

/-- The membership relation symbol of the language of set theory. -/
def memSymbol : setTheoryLanguage.Relations 2 := ⟨rfl⟩

/-! ## The target: independence of the Continuum Hypothesis -/

/-- **The Continuum Hypothesis is independent of ZFC.**

`ZFC` is an arbitrary theory in the language of set theory and `CH` an arbitrary sentence of that
language (in the intended reading, the axioms of Zermelo–Fraenkel set theory with choice and the
sentence expressing the Continuum Hypothesis).  The two deep inputs are supplied as hypotheses:

* `goedel`: if `ZFC` has a model, so does `ZFC + CH` (Gödel's constructible universe);
* `cohen`: if `ZFC` has a model, so does `ZFC + ¬CH` (Cohen's forcing).

Under the (necessary, by Gödel's second incompleteness theorem) assumption that `ZFC` is
consistent, the conclusion is that `CH` is independent of `ZFC`: `ZFC` entails neither `CH` nor
`¬CH`. -/
theorem CH_independent_statement
    (ZFC : setTheoryLanguage.Theory) (CH : setTheoryLanguage.Sentence)
    (consistent : ZFC.IsSatisfiable)
    (goedel : ZFC.IsSatisfiable → (ZFC ∪ {CH}).IsSatisfiable)
    (cohen : ZFC.IsSatisfiable → (ZFC ∪ {CH.not}).IsSatisfiable) :
    IndependentOf ZFC CH :=
  independentOf_of_isSatisfiable (goedel consistent) (cohen consistent)

/-- Consequence of the target for any sound proof calculus (in particular for the usual
first-order derivability relation): neither `CH` nor its negation is provable from `ZFC`. -/
theorem CH_not_provable_of_sound
    {Provable : setTheoryLanguage.Theory → setTheoryLanguage.Sentence → Prop}
    (sound : ∀ (S : setTheoryLanguage.Theory) (q : setTheoryLanguage.Sentence),
      Provable S q → S ⊨ᵇ q)
    (ZFC : setTheoryLanguage.Theory) (CH : setTheoryLanguage.Sentence)
    (consistent : ZFC.IsSatisfiable)
    (goedel : ZFC.IsSatisfiable → (ZFC ∪ {CH}).IsSatisfiable)
    (cohen : ZFC.IsSatisfiable → (ZFC ∪ {CH.not}).IsSatisfiable) :
    ¬ Provable ZFC CH ∧ ¬ Provable ZFC CH.not :=
  not_provable_of_independentOf sound (CH_independent_statement ZFC CH consistent goedel cohen)

/-! ## Non-vacuity checks -/

/-- The trivial structure for the language of set theory on any type: `∈` is interpreted as the
empty relation. -/
def trivialSetStructure (M : Type*) : setTheoryLanguage.Structure M where
  funMap := fun {_} f _ => (f : Empty).elim
  RelMap := fun {_} _ _ => False

/-- The hypotheses of `CH_independent_statement` are simultaneously satisfiable, so the target
theorem is not vacuous: there are a consistent theory and a sentence in the language of set
theory for which the Gödel-type and Cohen-type consistency hypotheses both hold. -/
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

theorem exists_independent_sentence :
    ∃ (L : FirstOrder.Language.{0, 0}) (T : L.Theory) (p : L.Sentence), IndependentOf T p := by
  refine ⟨FirstOrder.Language.empty, ∅, Sentence.cardGe FirstOrder.Language.empty 2,
    independentOf_of_isSatisfiable ?_ ?_⟩
  · letI : FirstOrder.Language.empty.Structure Bool := FirstOrder.Language.emptyStructure
    haveI : Bool ⊨ (∅ ∪ {Sentence.cardGe FirstOrder.Language.empty 2} :
        FirstOrder.Language.empty.Theory) := by
      rw [Theory.model_union_iff]
      refine ⟨inferInstance, Theory.model_singleton_iff.2 ?_⟩
      rw [Sentence.realize_cardGe]
      simp
    exact Theory.Model.isSatisfiable Bool
  · letI : FirstOrder.Language.empty.Structure Unit := FirstOrder.Language.emptyStructure
    haveI : Unit ⊨ (∅ ∪ {(Sentence.cardGe FirstOrder.Language.empty 2).not} :
        FirstOrder.Language.empty.Theory) := by
      rw [Theory.model_union_iff]
      refine ⟨inferInstance, Theory.model_singleton_iff.2 ?_⟩
      rw [Sentence.realize_not, Sentence.realize_cardGe]
      simp
    exact Theory.Model.isSatisfiable Unit

end Frontier

