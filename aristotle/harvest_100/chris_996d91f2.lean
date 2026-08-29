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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

universe u v w w'

namespace Frontier

open Cardinal
open FirstOrder FirstOrder.Language

/-!
## Part 1: the Continuum Hypothesis, stated inside Lean

`ContinuumHypothesis` is the usual statement "every uncountable set of reals has the
cardinality of the continuum".  We check (this is a theorem of ZFC, hence provable in Lean)
that it is equivalent to the arithmetical form `𝔠 = ℵ₁`.
-/

/-- The Continuum Hypothesis: every set of reals of cardinality greater than `ℵ₀` already has
the cardinality of the continuum. -/
def ContinuumHypothesis : Prop :=
  ∀ s : Set ℝ, ℵ₀ < #s → #s = 𝔠

/-- **The Continuum Hypothesis is equivalent to `𝔠 = ℵ₁`.**  This equivalence is a theorem of
ZFC, so it is provable outright (it is *not* the independent part). -/
theorem continuumHypothesis_iff_continuum_eq_aleph_one :
    ContinuumHypothesis ↔ (𝔠 : Cardinal.{0}) = ℵ₁ := by
  constructor
  · intro h
    refine le_antisymm ?_ aleph_one_le_continuum
    by_contra hlt
    push_neg at hlt
    obtain ⟨s, hs⟩ := (Cardinal.le_mk_iff_exists_set (c := ℵ₁) (α := ℝ)).1
      (by rw [Cardinal.mk_real]; exact hlt.le)
    have h1 : ℵ₀ < #s := by rw [hs]; exact aleph0_lt_aleph_one
    have h2 : #s = 𝔠 := h s h1
    rw [hs] at h2
    exact absurd h2 (ne_of_lt hlt)
  · intro h s hs
    have hle : #s ≤ 𝔠 := by
      have := Cardinal.mk_set_le s
      rwa [Cardinal.mk_real] at this
    have hge : ℵ₁ ≤ #s := by
      rw [← Cardinal.succ_aleph0]
      exact Order.succ_le_of_lt hs
    refine le_antisymm hle ?_
    rw [h]
    exact hge

/-!
## Part 2: independence, as a Lean-checked reduction

Mathlib contains no proof calculus for first-order logic, but it does contain the semantic
consequence relation `T ⊨ᵇ φ` ("every model of `T` satisfies `φ`"), which by Gödel's
completeness theorem coincides with provability from `T`.

The following theorem is the exact logical content of the Gödel–Cohen independence proof,
with the two hard model constructions taken as hypotheses:

* `Mgodel` is Gödel's constructible universe `L`, a model of ZFC in which CH holds;
* `Mcohen` is Cohen's forcing extension, a model of ZFC in which CH fails.

From these two models the theorem concludes that `ZFC` neither entails the sentence `ch` nor
its negation, and hence that `ZFC` is not a complete theory.  Everything below the two model
hypotheses is fully verified in Lean. -/

/-- **Independence of the Continuum Hypothesis (reduction to the two model constructions).**

Let `T` be a theory (think: ZFC in the language of set theory) and `ch` a sentence
(think: the first-order formalization of the Continuum Hypothesis).  If there is a model
`Mgodel` of `T` satisfying `ch` (Gödel's constructible universe) and a model `Mcohen` of `T`
satisfying `¬ch` (Cohen's forcing extension), then

* `T ⊭ ch`,
* `T ⊭ ¬ch`, and
* `T` is not complete,

i.e. `ch` is independent of `T`.  (By Gödel's completeness theorem, `⊨ᵇ` is equivalent to
provability, so this is exactly unprovability of `ch` and of `¬ch` from `T`.) -/
theorem CH_independent_statement {L : FirstOrder.Language.{u, v}} {T : L.Theory}
    {ch : L.Sentence}
    (Mgodel : Type w) [Nonempty Mgodel] [L.Structure Mgodel] [Mgodel ⊨ T]
    (hgodel : Mgodel ⊨ ch)
    (Mcohen : Type w') [Nonempty Mcohen] [L.Structure Mcohen] [Mcohen ⊨ T]
    (hcohen : Mcohen ⊨ Formula.not ch) :
    ¬ (T ⊨ᵇ ch) ∧ ¬ (T ⊨ᵇ Formula.not ch) ∧ ¬ T.IsComplete := by
  have hnotch : ¬ (T ⊨ᵇ ch) := by
    rw [Theory.models_iff_not_satisfiable]
    push_neg
    have : Mcohen ⊨ T ∪ {Formula.not ch} :=
      Theory.model_union_iff.2 ⟨inferInstance, Theory.model_singleton_iff.2 hcohen⟩
    exact Theory.Model.isSatisfiable Mcohen
  have hnotnotch : ¬ (T ⊨ᵇ Formula.not ch) := by
    rw [Theory.models_iff_not_satisfiable]
    push_neg
    have hgg : Mgodel ⊨ Formula.not (Formula.not ch) := by
      rw [Sentence.realize_not, Sentence.realize_not]
      exact not_not_intro hgodel
    have : Mgodel ⊨ T ∪ {Formula.not (Formula.not ch)} :=
      Theory.model_union_iff.2 ⟨inferInstance, Theory.model_singleton_iff.2 hgg⟩
    exact Theory.Model.isSatisfiable Mgodel
  refine ⟨hnotch, hnotnotch, ?_⟩
  rintro ⟨-, hcomplete⟩
  rcases hcomplete ch with h | h
  · exact hnotch h
  · exact hnotnotch h

/-- **Independence of the Continuum Hypothesis, consistency form.**

If `T ∪ {ch}` is satisfiable (Gödel: `ZFC + CH` has a model, namely the constructible
universe) and `T ∪ {¬ch}` is satisfiable (Cohen: `ZFC + ¬CH` has a model, obtained by
forcing), then `ch` is independent of `T`: neither `ch` nor `¬ch` is a consequence of `T`,
and `T` is incomplete. -/
theorem CH_independent_of_satisfiable {L : FirstOrder.Language.{u, v}} {T : L.Theory}
    {ch : L.Sentence}
    (hgodel : (T ∪ {ch}).IsSatisfiable)
    (hcohen : (T ∪ {Formula.not ch}).IsSatisfiable) :
    ¬ (T ⊨ᵇ ch) ∧ ¬ (T ⊨ᵇ Formula.not ch) ∧ ¬ T.IsComplete := by
  obtain ⟨Mg⟩ := hgodel
  obtain ⟨Mc⟩ := hcohen
  have hMg : Mg ⊨ T ∪ {ch} := Mg.is_model
  have hMc : Mc ⊨ T ∪ {Formula.not ch} := Mc.is_model
  have hMgT : Mg.Carrier ⊨ T := (Theory.model_union_iff.1 hMg).1
  have hMcT : Mc.Carrier ⊨ T := (Theory.model_union_iff.1 hMc).1
  have hg : Mg.Carrier ⊨ ch := Theory.model_singleton_iff.1 (Theory.model_union_iff.1 hMg).2
  have hc : Mc.Carrier ⊨ Formula.not ch :=
    Theory.model_singleton_iff.1 (Theory.model_union_iff.1 hMc).2
  exact CH_independent_statement Mg.Carrier hg Mc.Carrier hc

end Frontier

