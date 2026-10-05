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
def ContinuumHypothesis : Prop :=
  ∀ s : Set ℝ, ℵ₀ ≤ #s → #s = ℵ₀ ∨ #s = 𝔠

/-- `CH` is equivalent to `ℵ₁ = 𝔠`. -/
theorem continuumHypothesis_iff_aleph_one_eq_continuum :
    ContinuumHypothesis ↔ (ℵ₁ : Cardinal.{0}) = 𝔠 := by
  constructor
  · intro h
    refine le_antisymm Cardinal.aleph_one_le_continuum ?_
    by_contra hlt
    push_neg at hlt
    have h1 : (ℵ₁ : Cardinal.{0}) ≤ #ℝ := by
      rw [Cardinal.mk_real]; exact Cardinal.aleph_one_le_continuum
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.1 h1
    rcases h s (by rw [hs]; exact le_of_lt Cardinal.aleph0_lt_aleph_one) with h2 | h2 <;>
      rw [hs] at h2
    · exact absurd h2 (ne_of_gt Cardinal.aleph0_lt_aleph_one)
    · exact absurd h2 (ne_of_lt hlt)
  · intro h s hs
    by_cases hc : #s = ℵ₀
    · exact Or.inl hc
    · right
      have h1 : ℵ₀ < #s := lt_of_le_of_ne hs (Ne.symm hc)
      have h2 : (ℵ₁ : Cardinal.{0}) ≤ #s := by
        rw [← Cardinal.succ_aleph0]; exact Order.succ_le_of_lt h1
      have h3 : #s ≤ 𝔠 := by
        have := Cardinal.mk_set_le s; rwa [Cardinal.mk_real] at this
      exact le_antisymm h3 (h ▸ h2)

/-- `CH` is equivalent to the statement that no cardinal lies strictly between `ℵ₀` and `𝔠`. -/
theorem continuumHypothesis_iff_no_intermediate_cardinal :
    ContinuumHypothesis ↔ ∀ c : Cardinal.{0}, ℵ₀ < c → c < 𝔠 → False := by
  rw [continuumHypothesis_iff_aleph_one_eq_continuum]
  constructor
  · intro h c h1 h2
    have h3 : (ℵ₁ : Cardinal.{0}) ≤ c := by
      rw [← Cardinal.succ_aleph0]; exact Order.succ_le_of_lt h1
    rw [h] at h3
    exact absurd (lt_of_le_of_lt h3 h2) (lt_irrefl _)
  · intro h
    refine le_antisymm Cardinal.aleph_one_le_continuum ?_
    by_contra hlt
    push_neg at hlt
    exact absurd (h _ Cardinal.aleph0_lt_aleph_one hlt) not_false

/-!
## Part 2: independence in first-order logic
-/

open FirstOrder Language

/-- The relation symbols of the language of set theory: a single binary relation `∈`. -/
def setRel : ℕ → Type
  | 2 => Unit
  | _ => Empty

/-- The language of set theory: no function symbols, a single binary relation `∈`. -/
def setLang : Language := ⟨fun _ => Empty, setRel⟩

/-- The membership relation symbol of the language of set theory. -/
def memRel : setLang.Relations 2 := (() : Unit)

/-- A sentence `σ` is *independent* of a theory `T` when `T` proves neither `σ` nor `¬ σ`.
(By Gödel's completeness theorem, the semantic entailment `⊨ᵇ` used here coincides with
first-order provability.) -/
def IndependentOf {L : Language} (T : L.Theory) (σ : L.Sentence) : Prop :=
  ¬ T ⊨ᵇ σ ∧ ¬ T ⊨ᵇ σ.not

section Independence

variable {L : Language} {T : L.Theory} {σ : L.Sentence}

/-- Adding a doubly negated sentence to a theory is, for satisfiability purposes, the same as
adding the sentence itself. -/
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
theorem independentOf_iff_isSatisfiable :
    IndependentOf T σ ↔ (T ∪ {σ}).IsSatisfiable ∧ (T ∪ {σ.not}).IsSatisfiable := by
  rw [IndependentOf, Theory.models_iff_not_satisfiable, Theory.models_iff_not_satisfiable,
    not_not, not_not, isSatisfiable_union_not_not_iff]
  exact and_comm

/-- If both `T + σ` and `T + ¬σ` have models, then `σ` is independent of `T`. -/
theorem independentOf_of_isSatisfiable (h₁ : (T ∪ {σ}).IsSatisfiable)
    (h₂ : (T ∪ {σ.not}).IsSatisfiable) : IndependentOf T σ :=
  independentOf_iff_isSatisfiable.2 ⟨h₁, h₂⟩

end Independence

/-!
## Part 3: the target statement

The independence of the Continuum Hypothesis from `ZFC` is exactly the conjunction of the two
deep relative consistency theorems:

* Gödel (1938), the constructible universe `L`: `ZFC + CH` has a model;
* Cohen (1963), forcing: `ZFC + ¬CH` has a model.

The theorem below is the Lean-checked reduction: independence of `CH` from `ZFC` holds **iff**
these two model-existence statements hold. It is stated for an arbitrary theory `ZFC` and an
arbitrary sentence `CH` in the first-order language of set theory, so it applies in particular to
the usual axiomatisation of `ZFC` and to the usual first-order rendering of the Continuum
Hypothesis. The two inputs themselves (Gödel's and Cohen's constructions) are not formalised
here; they enter as the two satisfiability statements.
-/

/-- **The Continuum Hypothesis is independent of ZFC, reduced to Gödel's and Cohen's theorems.**

For any theory `ZFC` and any sentence `CH` in the first-order language of set theory, `CH` is
independent of `ZFC` (that is, `ZFC` entails neither `CH` nor `¬ CH`) if and only if both
`ZFC + CH` and `ZFC + ¬CH` are satisfiable — the former being Gödel's relative consistency result
via the constructible universe, the latter Cohen's via forcing. -/
theorem CH_independent_statement (ZFC : setLang.Theory) (CH : setLang.Sentence) :
    IndependentOf ZFC CH ↔
      ((ZFC ∪ {CH}).IsSatisfiable ∧ (ZFC ∪ {CH.not}).IsSatisfiable) :=
  independentOf_iff_isSatisfiable

/-- The independence of `CH` from `ZFC` in implication form: given Gödel's relative consistency
result and Cohen's relative consistency result, `ZFC` entails neither `CH` nor its negation. -/
theorem CH_independent_of_ZFC (ZFC : setLang.Theory) (CH : setLang.Sentence)
    (godel : (ZFC ∪ {CH}).IsSatisfiable) (cohen : (ZFC ∪ {CH.not}).IsSatisfiable) :
    ¬ ZFC ⊨ᵇ CH ∧ ¬ ZFC ⊨ᵇ CH.not :=
  (CH_independent_statement ZFC CH).2 ⟨godel, cohen⟩

/-!
## Part 4: the criterion is non-vacuous

A fully checked instance of the independence criterion in the language of set theory: the
sentence "there exist two distinct sets" is independent of the empty theory, since a one-element
`∈`-structure refutes it while a two-element `∈`-structure satisfies it.
-/

/-- The trivial `∈`-structure (empty membership relation) on any type. -/
def trivialSetStructure (M : Type) : setLang.Structure M where
  funMap {_} f := (f : Empty).elim
  RelMap {_} _ _ := False

attribute [local instance] trivialSetStructure

/-- The sentence "there exist two distinct sets". -/
def twoElements : setLang.Sentence :=
  ∃' ∃' ∼(FirstOrder.Language.Term.var (Sum.inr 0) =' FirstOrder.Language.Term.var (Sum.inr 1))

theorem isSatisfiable_twoElements :
    ((∅ : setLang.Theory) ∪ {twoElements}).IsSatisfiable := by
  have h : Bool ⊨ (∅ : setLang.Theory) ∪ {twoElements} := by
    rw [Theory.model_union_iff, Theory.model_singleton_iff]
    refine ⟨inferInstance, ?_⟩
    simp [twoElements, Sentence.Realize, Formula.Realize, Fin.snoc]
  exact ⟨⟨Bool⟩⟩

theorem isSatisfiable_not_twoElements :
    ((∅ : setLang.Theory) ∪ {twoElements.not}).IsSatisfiable := by
  have h : Unit ⊨ (∅ : setLang.Theory) ∪ {twoElements.not} := by
    rw [Theory.model_union_iff, Theory.model_singleton_iff]
    refine ⟨inferInstance, ?_⟩
    simp [twoElements, Sentence.Realize, Formula.Realize]
  exact ⟨⟨Unit⟩⟩

/-- Non-vacuity of the independence criterion: some sentence of the language of set theory really
is independent of some theory, with both witnessing models exhibited. -/
theorem independentOf_twoElements : IndependentOf (∅ : setLang.Theory) twoElements :=
  independentOf_of_isSatisfiable isSatisfiable_twoElements isSatisfiable_not_twoElements

end Frontier

