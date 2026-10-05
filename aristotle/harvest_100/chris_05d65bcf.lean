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

open scoped Classical

set_option maxHeartbeats 1000000

open Cardinal FirstOrder Language

namespace Frontier

/-! ## Part 1: the Continuum Hypothesis as a statement about sets of reals -/

/-- The Continuum Hypothesis, phrased inside Lean's ambient set theory: every set of reals
that is uncountable has the cardinality of the continuum. -/
def ContinuumHypothesis : Prop := ∀ s : Set ℝ, ℵ₀ < #s → #s = 𝔠

/-- `ContinuumHypothesis` is equivalent to the usual cardinal-arithmetic form `𝔠 = ℵ₁`. -/
theorem CH_iff_continuum_eq_aleph_one :
    ContinuumHypothesis ↔ (𝔠 : Cardinal.{0}) = ℵ_ 1 := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (Cardinal.le_mk_iff_exists_set (c := ℵ_ 1) (α := ℝ)).1
      (by simpa [Cardinal.mk_real] using Cardinal.aleph_one_le_continuum)
    have hcont := h s (by rw [hs]; exact Cardinal.aleph0_lt_aleph_one)
    rw [hs] at hcont
    exact hcont.symm
  · intro h s hs
    have h1 : #s ≤ 𝔠 := by simpa [Cardinal.mk_real] using Cardinal.mk_set_le s
    have h2 : ℵ_ 1 ≤ #s := by
      rw [← Cardinal.succ_aleph0]
      exact Order.succ_le_of_lt hs
    rw [h] at h1 ⊢
    exact le_antisymm h1 h2

/-- The negation of the Continuum Hypothesis says exactly that there is a set of reals of
strictly intermediate cardinality. -/
theorem not_CH_iff_exists_intermediate :
    ¬ ContinuumHypothesis ↔ ∃ s : Set ℝ, ℵ₀ < #s ∧ #s < 𝔠 := by
  constructor
  · intro h
    simp only [ContinuumHypothesis, not_forall] at h
    obtain ⟨s, hs, hne⟩ := h
    have h1 : #s ≤ 𝔠 := by simpa [Cardinal.mk_real] using Cardinal.mk_set_le s
    exact ⟨s, hs, lt_of_le_of_ne h1 hne⟩
  · rintro ⟨s, hs, hlt⟩ h
    exact absurd (h s hs) hlt.ne

/-! ## Part 2: independence, formalized in first-order logic

Mathlib's `T ⊨ᵇ φ` is the semantic consequence relation; by Gödel's completeness theorem it
coincides with first-order provability, so `IndependentOf T φ` below is the usual notion:
neither `φ` nor its negation is provable from `T`. -/

/-- The first-order language of set theory: no function or constant symbols, and a single
binary relation symbol (membership). -/
def setTheoryLang : Language where
  Functions := fun _ => Empty
  Relations := fun n => if n = 2 then Unit else Empty

/-- The membership relation symbol of the language of set theory. -/
def memSymbol : setTheoryLang.Relations 2 := (by exact () : Unit)

/-- A sentence `φ` is independent of a theory `T` when neither `φ` nor `¬ φ` is a consequence
of `T`. -/
def IndependentOf {L : Language} (T : L.Theory) (φ : L.Sentence) : Prop :=
  ¬ T ⊨ᵇ φ ∧ ¬ T ⊨ᵇ φ.not

/-- Independence is exactly the joint consistency of `T + φ` and `T + ¬φ`. This is the precise
sense in which Gödel's constructible universe (a model of ZFC + CH) together with Cohen's
forcing extension (a model of ZFC + ¬CH) yield the independence of CH. -/
theorem independentOf_iff_isSatisfiable {L : Language} (T : L.Theory) (φ : L.Sentence) :
    IndependentOf T φ ↔ (T ∪ {φ}).IsSatisfiable ∧ (T ∪ {φ.not}).IsSatisfiable := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [Theory.models_iff_not_satisfiable, not_not] at h1
    rw [Theory.models_iff_not_satisfiable, not_not] at h2
    refine ⟨?_, h1⟩
    obtain ⟨M⟩ := h2
    have hM := M.is_model
    rw [Theory.model_union_iff] at hM
    have hnn : M ⊨ φ.not.not := Theory.model_singleton_iff.1 hM.2
    haveI : (M : Type _) ⊨ (T ∪ {φ}) := by
      rw [Theory.model_union_iff]
      exact ⟨hM.1, Theory.model_singleton_iff.2 (by simpa using hnn)⟩
    exact Theory.Model.isSatisfiable M
  · rintro ⟨godel, cohen⟩
    refine ⟨?_, ?_⟩
    · rw [Theory.models_iff_not_satisfiable]
      exact fun h => h cohen
    · rw [Theory.models_iff_not_satisfiable]
      intro h
      obtain ⟨M⟩ := godel
      have hM := M.is_model
      rw [Theory.model_union_iff] at hM
      have hch : M ⊨ φ := Theory.model_singleton_iff.1 hM.2
      haveI : (M : Type _) ⊨ (T ∪ {φ.not.not}) := by
        rw [Theory.model_union_iff]
        exact ⟨hM.1, Theory.model_singleton_iff.2 (by simpa using hch)⟩
      exact h (Theory.Model.isSatisfiable M)

/-- A theory with an independent sentence is not complete. -/
theorem not_isComplete_of_independentOf {L : Language} {T : L.Theory} {φ : L.Sentence}
    (h : IndependentOf T φ) : ¬ T.IsComplete := by
  intro hc
  rcases hc.2 φ with h1 | h2
  · exact h.1 h1
  · exact h.2 h2

/-- **Independence of the Continuum Hypothesis (Gödel + Cohen), as a Lean-checked reduction.**

Working in the first-order language of set theory, let `ZFC` be any theory and `ch` any
sentence (intended: the axioms of ZFC and a formalization of the Continuum Hypothesis).
Gödel's theorem provides a model of `ZFC + CH` (the constructible universe `L`) and Cohen's
forcing construction provides a model of `ZFC + ¬CH`. Given exactly these two inputs, `ch` is
independent of `ZFC`: neither `ch` nor `¬ ch` is a consequence of (equivalently, by Gödel
completeness, provable from) `ZFC`; in particular `ZFC` is not a complete theory.

Conversely (see `independentOf_iff_isSatisfiable`) independence is *equivalent* to the joint
satisfiability of `ZFC + CH` and `ZFC + ¬CH`, so the two model constructions are not merely
sufficient but necessary. -/
theorem CH_independent_statement (ZFC : setTheoryLang.Theory) (ch : setTheoryLang.Sentence)
    (godel : (ZFC ∪ {ch}).IsSatisfiable)
    (cohen : (ZFC ∪ {ch.not}).IsSatisfiable) :
    IndependentOf ZFC ch ∧ ¬ ZFC.IsComplete := by
  have h : IndependentOf ZFC ch :=
    (independentOf_iff_isSatisfiable ZFC ch).2 ⟨godel, cohen⟩
  exact ⟨h, not_isComplete_of_independentOf h⟩

end Frontier

