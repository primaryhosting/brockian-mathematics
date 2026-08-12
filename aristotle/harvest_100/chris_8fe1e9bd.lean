/-
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header
-- above is written as a plain block comment.)

import Mathlib

set_option autoImplicit false

open Cardinal FirstOrder Language

namespace Frontier

/-! ## Part 1: the Continuum Hypothesis as a statement about cardinals

Inside Lean's own (ZFC-like) ambient set theory we can state CH directly:
there is no cardinal strictly between `ℵ₀` and `𝔠 = 2 ^ ℵ₀`.  We check that this
is equivalent to the usual formulation `𝔠 = ℵ₁`, and to the "no set of reals of
intermediate cardinality" formulation.  These equivalences are theorems of ZFC
(they are proved outright below); it is CH itself that is independent. -/

/-- The Continuum Hypothesis, stated for cardinals: no cardinal lies strictly
between `ℵ₀` and the cardinality of the continuum. -/
def CardinalCH : Prop := ∀ c : Cardinal.{0}, ℵ₀ < c → c < 𝔠 → False

/-- CH is equivalent to `𝔠 = ℵ₁`. -/
theorem cardinalCH_iff_continuum_eq_aleph_one :
    CardinalCH ↔ (𝔠 : Cardinal.{0}) = ℵ₁ := by
  constructor
  · intro h
    rcases lt_or_eq_of_le (aleph_one_le_continuum : (ℵ₁ : Cardinal.{0}) ≤ 𝔠) with hlt | heq
    · exact (h ℵ₁ aleph0_lt_aleph_one hlt).elim
    · exact heq.symm
  · intro h c hc0 hcc
    rw [h] at hcc
    have : ℵ₁ ≤ c := by
      rw [← succ_aleph0]
      exact Order.succ_le_of_lt hc0
    exact absurd hcc (not_lt.2 this)

/-- CH is equivalent to: every infinite set of reals is either countable or of the
cardinality of the continuum. -/
theorem cardinalCH_iff_sets_of_reals :
    CardinalCH ↔ ∀ s : Set ℝ, s.Infinite → #s = ℵ₀ ∨ #s = 𝔠 := by
  constructor
  · intro h s hs
    have h1 : ℵ₀ ≤ #s := Cardinal.infinite_iff.1 hs.to_subtype
    have h2 : #s ≤ 𝔠 := by
      have := Cardinal.mk_set_le s
      rwa [Cardinal.mk_real] at this
    rcases eq_or_lt_of_le h1 with e | lt
    · exact Or.inl e.symm
    · rcases eq_or_lt_of_le h2 with e | lt2
      · exact Or.inr e
      · exact (h _ lt lt2).elim
  · intro h c hc0 hcc
    have hle : c ≤ #ℝ := by rw [Cardinal.mk_real]; exact hcc.le
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.1 hle
    have hinf : s.Infinite :=
      Set.infinite_coe_iff.1 (Cardinal.infinite_iff.2 (hs ▸ hc0.le))
    rcases h s hinf with e | e
    · rw [hs] at e; exact absurd e (ne_of_gt hc0)
    · rw [hs] at e; exact absurd e (ne_of_lt hcc)

/-! ## Part 2: independence, model-theoretically

Mathlib has no proof calculus for first-order logic, but it has the semantic
consequence relation `T ⊨ᵇ φ`, which by Gödel's completeness theorem coincides
with provability from `T`.  "`φ` is independent of `T`" therefore means:
neither `φ` nor `¬ φ` is a semantic consequence of `T`. -/

/-- The relation symbols of the language of set theory: a single binary symbol `∈`. -/
def memRel : ℕ → Type
  | 2 => Unit
  | _ => Empty

/-- The language of set theory: no function symbols, a single binary relation symbol `∈`. -/
def setLang : Language := ⟨fun _ => Empty, memRel⟩

/-- A sentence `φ` is *independent* of a theory `T` when neither `φ` nor its
negation is a consequence of `T`. -/
def Independent {L : Language} (T : L.Theory) (φ : L.Sentence) : Prop :=
  ¬ T ⊨ᵇ φ ∧ ¬ T ⊨ᵇ φ.not

/-- If `T ∪ {φ}` has a model, then `¬ φ` is not a consequence of `T`. -/
theorem not_models_not_of_isSatisfiable {L : Language} {T : L.Theory} {φ : L.Sentence}
    (h : (T ∪ {φ}).IsSatisfiable) : ¬ T ⊨ᵇ φ.not := by
  intro hmod
  obtain ⟨M⟩ := h
  haveI : (M : Type _) ⊨ T := M.is_model.mono Set.subset_union_left
  have hφ : (M : Type _) ⊨ φ :=
    Theory.realize_sentence_of_mem (T ∪ {φ}) (Set.mem_union_right _ rfl)
  exact (Sentence.realize_not _).1 (hmod.realize_sentence M) hφ

/-- **Independence from two models.**  If a theory `T` has a model satisfying `φ`
and a model satisfying `¬ φ`, then `φ` is independent of `T`. -/
theorem independent_of_two_models {L : Language} {T : L.Theory} {φ : L.Sentence}
    (hpos : (T ∪ {φ}).IsSatisfiable) (hneg : (T ∪ {φ.not}).IsSatisfiable) :
    Independent T φ :=
  ⟨fun hm => ((Theory.models_iff_not_satisfiable φ).1 hm) hneg,
    not_models_not_of_isSatisfiable hpos⟩

/-- A theory with an independent sentence is incomplete. -/
theorem not_isComplete_of_independent {L : Language} {T : L.Theory} {φ : L.Sentence}
    (h : Independent T φ) : ¬ T.IsComplete := by
  rintro ⟨-, hdec⟩
  rcases hdec φ with hp | hn
  · exact h.1 hp
  · exact h.2 hn

/-- **The Continuum Hypothesis is independent of ZFC.**

Here `ZFC` is a theory in the language of set theory and `CH` a sentence of that
language.  The two hypotheses are exactly the two halves of the independence
proof:

* `godel` : Gödel (1938) — the constructible universe `L` is a model of `ZFC + CH`;
* `cohen` : Cohen (1963) — a forcing extension gives a model of `ZFC + ¬CH`.

From these, neither `CH` nor `¬CH` is a semantic consequence of `ZFC`, i.e. (by
the Gödel completeness theorem) neither is provable from `ZFC`. -/
theorem CH_independent_statement
    (ZFC : setLang.Theory) (CH : setLang.Sentence)
    (godel : (ZFC ∪ {CH}).IsSatisfiable)
    (cohen : (ZFC ∪ {CH.not}).IsSatisfiable) :
    Independent ZFC CH :=
  independent_of_two_models godel cohen

/-- In particular, such a `ZFC` is an incomplete theory. -/
theorem ZFC_not_isComplete
    (ZFC : setLang.Theory) (CH : setLang.Sentence)
    (godel : (ZFC ∪ {CH}).IsSatisfiable)
    (cohen : (ZFC ∪ {CH.not}).IsSatisfiable) :
    ¬ ZFC.IsComplete :=
  not_isComplete_of_independent (CH_independent_statement ZFC CH godel cohen)

/-- The hypotheses of `independent_of_two_models` are not vacuous: independent
sentences really do exist.  Over the empty language, the empty theory decides
neither "there are at least two elements" nor its negation, as witnessed by the
two-element model `Bool` and the one-element model `Unit`. -/
theorem exists_independent_sentence :
    ∃ φ : Language.empty.Sentence, Independent (∅ : Language.empty.Theory) φ := by
  haveI : Language.empty.Structure Bool := Language.emptyStructure
  haveI : Language.empty.Structure Unit := Language.emptyStructure
  refine ⟨Sentence.cardGe Language.empty 2, independent_of_two_models ?_ ?_⟩
  · haveI : (Bool : Type) ⊨ (∅ ∪ {Sentence.cardGe Language.empty 2} : Language.empty.Theory) := by
      refine (Theory.model_iff _).2 ?_
      intro ψ hψ
      simp only [Set.empty_union, Set.mem_singleton_iff] at hψ
      subst hψ
      rw [Sentence.realize_cardGe]
      simp
    exact Theory.Model.isSatisfiable Bool
  · haveI : (Unit : Type) ⊨
        (∅ ∪ {(Sentence.cardGe Language.empty 2).not} : Language.empty.Theory) := by
      refine (Theory.model_iff _).2 ?_
      intro ψ hψ
      simp only [Set.empty_union, Set.mem_singleton_iff] at hψ
      subst hψ
      rw [Sentence.realize_not, Sentence.realize_cardGe]
      simp
    exact Theory.Model.isSatisfiable Unit

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

