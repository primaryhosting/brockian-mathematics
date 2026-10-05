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
def Independent {L : Language} (T : L.Theory) (s0 : L.Sentence) : Prop :=
  ¬ T ⊨ᵇ s0 ∧ ¬ T ⊨ᵇ s0.not

section General

variable {L : Language} {T : L.Theory} {s0 : L.Sentence}

/-- Satisfiability is invariant under replacing `¬¬s0` by `s0`. -/
theorem isSatisfiable_union_not_not_iff :
    (T ∪ {s0.not.not}).IsSatisfiable ↔ (T ∪ {s0}).IsSatisfiable := by
  constructor
  · rintro ⟨M⟩
    have hM : (M : Type _) ⊨ T ∪ {s0.not.not} := M.is_model
    haveI : (M : Type _) ⊨ T ∪ {s0} := by
      rw [Theory.model_iff] at hM ⊢
      intro psi hpsi
      rcases hpsi with hpsi | hpsi
      · exact hM psi (Or.inl hpsi)
      · have h := hM _ (Or.inr (Set.mem_singleton _))
        simp only [Set.mem_singleton_iff] at hpsi
        subst hpsi
        simpa [Sentence.Realize] using h
    exact ⟨Theory.ModelType.of _ (M : Type _)⟩
  · rintro ⟨M⟩
    have hM : (M : Type _) ⊨ T ∪ {s0} := M.is_model
    haveI : (M : Type _) ⊨ T ∪ {s0.not.not} := by
      rw [Theory.model_iff] at hM ⊢
      intro psi hpsi
      rcases hpsi with hpsi | hpsi
      · exact hM psi (Or.inl hpsi)
      · have h := hM _ (Or.inr (Set.mem_singleton _))
        simp only [Set.mem_singleton_iff] at hpsi
        subst hpsi
        simpa [Sentence.Realize] using h
    exact ⟨Theory.ModelType.of _ (M : Type _)⟩

/-- **The independence criterion.**  A sentence is independent of a theory exactly when both
the theory together with the sentence and the theory together with its negation have models.
This is the semantic form of the statement "`T` proves neither `s0` nor `¬s0`". -/
theorem independent_iff_isSatisfiable :
    Independent T s0 ↔ (T ∪ {s0}).IsSatisfiable ∧ (T ∪ {s0.not}).IsSatisfiable := by
  rw [Independent, Theory.models_iff_not_satisfiable, Theory.models_iff_not_satisfiable,
    not_not, not_not, isSatisfiable_union_not_not_iff, and_comm]

/-- If a theory has a model of `s0` and a model of `¬s0`, then `s0` is independent of it. -/
theorem independent_of_models (h₁ : (T ∪ {s0}).IsSatisfiable)
    (h₂ : (T ∪ {s0.not}).IsSatisfiable) : Independent T s0 :=
  independent_iff_isSatisfiable.2 ⟨h₁, h₂⟩

/-- An independent sentence is in particular not entailed by the theory. -/
theorem Independent.not_models (h : Independent T s0) : ¬ T ⊨ᵇ s0 := h.1

/-- The negation of an independent sentence is not entailed by the theory either. -/
theorem Independent.not_models_not (h : Independent T s0) : ¬ T ⊨ᵇ s0.not := h.2

/-- An independent sentence witnesses incompleteness of the theory. -/
theorem Independent.not_isComplete (h : Independent T s0) : ¬ T.IsComplete := by
  rintro ⟨-, hc⟩
  rcases hc s0 with h' | h'
  · exact h.1 h'
  · exact h.2 h'

/-- Independence is symmetric in `s0` and `¬s0`. -/
theorem Independent.not (h : Independent T s0) : Independent T s0.not := by
  rw [independent_iff_isSatisfiable] at h ⊢
  exact ⟨h.2, isSatisfiable_union_not_not_iff.2 h.1⟩

end General

/-! ### The first-order language of set theory -/

/-- The relation symbols of the language of set theory: a single binary symbol `∈`. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/
def setLanguage : Language := ⟨fun _ => Empty, memRel⟩

/-- The membership symbol of the language of set theory. -/
def memSymbol : setLanguage.Relations 2 := memRel.mem

/-- The atomic formula `t₁ ∈ t₂` of the language of set theory. -/
def memFormula {n : ℕ} (t₁ t₂ : setLanguage.Term (Empty ⊕ Fin n)) :
    setLanguage.BoundedFormula Empty n :=
  memSymbol.boundedFormula₂ t₁ t₂

/-! ### The target statement -/

/-- **Independence of the Continuum Hypothesis (semantic form).**

Let `ZFC` be any theory in the first-order language of set theory and let `CH` be any sentence
of that language.  Gödel's constructible-universe argument provides a model of `ZFC + CH`
(hypothesis `goedel`), and Cohen's forcing argument provides a model of `ZFC + ¬CH`
(hypothesis `cohen`).  From these two relative consistency results the independence of `CH`
over `ZFC` follows: `ZFC` entails neither `CH` nor `¬CH`, and hence — by the completeness
theorem — proves neither.  This is the Lean-checked reduction of the independence of the
Continuum Hypothesis to the two model constructions of Gödel and Cohen. -/
theorem CH_independent_statement (ZFC : setLanguage.Theory) (CH : setLanguage.Sentence)
    (goedel : (ZFC ∪ {CH}).IsSatisfiable)
    (cohen : (ZFC ∪ {CH.not}).IsSatisfiable) :
    Independent ZFC CH ∧ ¬ ZFC.IsComplete :=
  ⟨independent_of_models goedel cohen,
    (independent_of_models goedel cohen).not_isComplete⟩

/-! ### A fully verified base case

To show that the notion of independence above is not vacuous, we verify a concrete instance
inside the language of set theory: the sentence `∃ x, ∀ y, ¬ (y ∈ x)` ("there is an empty
set") is independent of the empty theory.  A model is given by `ℕ` with `∈` interpreted as
`<` (the element `0` has nothing below it), a counter-model by `ℤ` with `∈` interpreted as
`<` (no integer is minimal). -/

/-- `∃ x, ∀ y, ¬ (y ∈ x)`: the sentence asserting the existence of an empty set. -/
def emptySetSentence : setLanguage.Sentence :=
  BoundedFormula.ex (BoundedFormula.all (memFormula (&1) (&0)).not)

/-- Interpretation of the language of set theory in any preorder-like type, sending `∈` to `<`. -/
def ltStructure (M : Type*) [LT M] : setLanguage.Structure M where
  funMap {n} f := by cases n <;> exact f.elim
  RelMap {n} r := by
    cases r with
    | mem => exact fun v => v 0 < v 1

/-- In a type ordered by `<`, the sentence `emptySetSentence` says exactly that there is a
minimal element. -/
theorem realize_emptySetSentence (M : Type) [LT M] :
    letI := ltStructure M
    (M ⊨ emptySetSentence) ↔ ∃ x : M, ∀ y : M, ¬ y < x := by
  letI := ltStructure M
  simp only [emptySetSentence, memFormula, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_ex, BoundedFormula.realize_all, BoundedFormula.realize_not,
    BoundedFormula.realize_rel₂]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun y => by simpa [ltStructure, memSymbol, Fin.snoc] using hx y⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, fun y => by simpa [ltStructure, memSymbol, Fin.snoc] using hx y⟩

/-- `ℕ`, with `∈` read as `<`, is a model of "there is an empty set". -/
theorem isSatisfiable_emptySetSentence :
    ((∅ : setLanguage.Theory) ∪ {emptySetSentence}).IsSatisfiable := by
  letI := ltStructure ℕ
  haveI : ℕ ⊨ (∅ : setLanguage.Theory) ∪ {emptySetSentence} := by
    rw [Theory.model_iff]
    intro psi hpsi
    simp only [Set.empty_union, Set.mem_singleton_iff] at hpsi
    subst hpsi
    exact (realize_emptySetSentence ℕ).2 ⟨0, fun y => Nat.not_lt_zero y⟩
  exact ⟨Theory.ModelType.of _ ℕ⟩

/-- `ℤ`, with `∈` read as `<`, is a model of the negation of "there is an empty set". -/
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
theorem emptySetSentence_independent :
    Independent (∅ : setLanguage.Theory) emptySetSentence :=
  independent_of_models isSatisfiable_emptySetSentence isSatisfiable_not_emptySetSentence

/-! ### The Continuum Hypothesis in Mathlib's cardinal arithmetic

The sentence `CH` above is the first-order rendering, inside a model of set theory, of the
following statement about cardinals: there is no cardinal strictly between `ℵ₀` and the
cardinality `𝔠` of the continuum.  We record the standard reformulation `𝔠 = ℵ₁`, which is
provable outright (the independence lies in whether the statement itself holds). -/

open Cardinal in
/-- The Continuum Hypothesis, stated for cardinals: no cardinal lies strictly between `ℵ₀`
and `𝔠`. -/
def ContinuumHypothesis : Prop :=
  ∀ c : Cardinal.{0}, ℵ₀ < c → c < Cardinal.continuum.{0} → False

open Cardinal in
/-- The Continuum Hypothesis holds if and only if `𝔠 = ℵ₁`. -/
theorem continuumHypothesis_iff_continuum_eq_aleph_one :
    ContinuumHypothesis ↔ Cardinal.continuum.{0} = Cardinal.aleph 1 := by
  constructor
  · intro h
    rcases eq_or_lt_of_le Cardinal.aleph_one_le_continuum.{0} with he | hl
    · exact he.symm
    · exact (h _ Cardinal.aleph0_lt_aleph_one hl).elim
  · intro h c h0 hc
    rw [h, ← Cardinal.succ_aleph0, Order.lt_succ_iff] at hc
    exact absurd h0 (not_lt.2 hc)

end Frontier

