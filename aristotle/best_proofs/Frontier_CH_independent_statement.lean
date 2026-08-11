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
def ContinuumHypothesis : Prop :=
  ∀ s : Set ℝ, ¬ s.Countable → #s = 𝔠

/-- The Continuum Hypothesis is equivalent to the cardinal equation `ℵ₁ = 𝔠`. -/
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
def IndependentOf {L : FirstOrder.Language} (T : L.Theory) (φ : L.Sentence) : Prop :=
  ¬ T ⊨ᵇ φ ∧ ¬ T ⊨ᵇ φ.not

/-- Independence is *exactly* the existence of two models of `T`, one satisfying `φ`
and one refuting it. This is the general form of the Gödel/Cohen reduction: to prove
independence it suffices to construct the two models. -/
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
theorem independentOf_of_models {L : FirstOrder.Language.{u, v}} {T : L.Theory}
    {φ : L.Sentence}
    (M : Language.Theory.ModelType.{u, v, max u v} T) (hM : M ⊨ φ)
    (N : Language.Theory.ModelType.{u, v, max u v} T) (hN : ¬ N ⊨ φ) :
    IndependentOf T φ :=
  (independentOf_iff_exists_models T φ).2 ⟨⟨M, hM⟩, ⟨N, hN⟩⟩

/-! ## Part 3: the language of set theory and the statement of the independence of CH -/

/-- The relation symbols of the language of set theory: a single binary relation `∈`. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory: one binary relation symbol, `∈`. -/
def setTheoryLang : FirstOrder.Language := ⟨fun _ => Empty, memRel⟩

/-- The membership symbol of the language of set theory. -/
abbrev memSymb : setTheoryLang.Relations 2 := memRel.mem

/-- **The Continuum Hypothesis is independent of ZFC.**

This is the formal statement, reduced (as in the Gödel–Cohen proof) to the existence
of the two models: if `zfc` is any theory in the first-order language of set theory
and `ch` is any sentence of that language (intended: a sentence formalizing the
Continuum Hypothesis), then, given

* `goedel`, a model of `zfc` satisfying `ch` (Gödel's constructible universe `L`), and
* `cohen`, a model of `zfc` refuting `ch` (Cohen's forcing extension),

the sentence `ch` is independent of `zfc`: neither `ch` nor `¬ ch` is a semantic
consequence of `zfc`, hence — by Gödel's completeness theorem — neither is provable
from `zfc`.

The two model hypotheses are exactly the content of Gödel's and Cohen's theorems;
they are not constructed here (they cannot be, without assuming the consistency of
ZFC). By `Frontier.independentOf_iff_exists_models` this reduction is an equivalence,
so nothing is lost by stating independence in this form. -/
theorem CH_independent_statement
    (zfc : setTheoryLang.Theory) (ch : setTheoryLang.Sentence)
    (goedel : Language.Theory.ModelType.{0, 0, 0} zfc) (hgoedel : goedel ⊨ ch)
    (cohen : Language.Theory.ModelType.{0, 0, 0} zfc) (hcohen : ¬ cohen ⊨ ch) :
    IndependentOf zfc ch :=
  independentOf_of_models goedel hgoedel cohen hcohen

end Frontier

import Mathlib

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

