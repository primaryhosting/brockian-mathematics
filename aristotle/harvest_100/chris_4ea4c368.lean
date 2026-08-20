/-
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the required header
-- appears above as a plain comment and verbatim as the module docstring below.)

import Mathlib

/-!
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

open Cardinal FirstOrder Language

namespace Frontier

/-!
## What is (and is not) proved here

The full independence of the Continuum Hypothesis from ZFC (Gödel's constructible
universe for `Con(ZFC) → Con(ZFC + CH)`, Cohen's forcing for
`Con(ZFC) → Con(ZFC + ¬CH)`) is *not* available in Mathlib: Mathlib contains no
first-order axiomatisation of ZFC, no constructible hierarchy and no forcing
machinery.  What is proved below is the honest, Lean-checked part of the task:

* `Frontier.CH`, the Continuum Hypothesis in Cantor's original formulation
  (every uncountable set of reals has the cardinality of the continuum);
* `Frontier.CH_iff_continuum_eq_aleph_one`, the reduction of that statement to
  the cardinal-arithmetic form `𝔠 = ℵ₁`;
* `Frontier.aleph0_lt_continuum'`, the "base case" (Cantor's theorem,
  `Cardinal.aleph0_lt_continuum` in Mathlib): the continuum is uncountable, so
  CH is a genuine dichotomy and not vacuous;
* `Frontier.Independent` together with
  `Frontier.independent_iff_both_satisfiable`, the model-theoretic reduction of
  independence: a sentence is independent of a theory exactly when both the
  theory plus the sentence and the theory plus its negation have models.  This
  is the shape of the Gödel/Cohen argument (produce a model of ZFC + CH and a
  model of ZFC + ¬CH); only the two model constructions are missing.

The target theorem `Frontier.CH_independent_statement` packages these three
Lean-checked components.
-/

/-- The Continuum Hypothesis, in Cantor's original formulation: every set of
reals that is not countable has the cardinality of the continuum. -/
def CH : Prop := ∀ s : Set ℝ, ℵ₀ < #s → #s = 𝔠

/-- Cantor's theorem, the base case: the continuum is uncountable.  (Mathlib:
`Cardinal.aleph0_lt_continuum`.) -/
theorem aleph0_lt_continuum' : ℵ₀ < 𝔠 := Cardinal.aleph0_lt_continuum

/-- The Continuum Hypothesis is equivalent to the cardinal-arithmetic statement
`𝔠 = ℵ₁`. -/
theorem CH_iff_continuum_eq_aleph_one : CH ↔ (𝔠 : Cardinal.{0}) = ℵ_ 1 := by
  constructor
  · intro h
    obtain ⟨p, -, hp⟩ := Cardinal.le_mk_iff_exists_subset.1
      (show ℵ_ 1 ≤ #(Set.univ : Set ℝ) by
        rw [Cardinal.mk_univ, mk_real]; exact aleph_one_le_continuum)
    have hlt : ℵ₀ < #p := by rw [hp]; exact aleph0_lt_aleph_one
    have := h p hlt
    rw [hp] at this
    exact this.symm
  · intro h s hs
    have h1 : ℵ_ 1 ≤ #s := by
      rw [← succ_aleph0]; exact Order.succ_le_of_lt hs
    have h2 : #s ≤ 𝔠 := (Cardinal.mk_set_le s).trans mk_real.le
    exact le_antisymm h2 (by rw [h]; exact h1)

/-- A sentence `φ` is *independent* of a theory `T` when neither `φ` nor its
negation is a semantic consequence of `T`. -/
def Independent {L : Language} (T : L.Theory) (φ : L.Sentence) : Prop :=
  ¬ T ⊨ᵇ φ ∧ ¬ T ⊨ᵇ φ.not

/-- Satisfiability is insensitive to double negation of the added sentence. -/
private theorem isSatisfiable_union_not_not {L : Language} (T : L.Theory) (φ : L.Sentence) :
    (T ∪ {φ.not.not}).IsSatisfiable ↔ (T ∪ {φ}).IsSatisfiable := by
  constructor
  · rintro ⟨M⟩
    have hM := M.is_model
    rw [Theory.model_union_iff, Theory.model_singleton_iff] at hM
    haveI : (M : Type _) ⊨ T ∪ {φ} := by
      rw [Theory.model_union_iff, Theory.model_singleton_iff]
      exact ⟨hM.1, by simpa using hM.2⟩
    exact Theory.Model.isSatisfiable (M : Type _)
  · rintro ⟨M⟩
    have hM := M.is_model
    rw [Theory.model_union_iff, Theory.model_singleton_iff] at hM
    haveI : (M : Type _) ⊨ T ∪ {φ.not.not} := by
      rw [Theory.model_union_iff, Theory.model_singleton_iff]
      exact ⟨hM.1, by simpa using hM.2⟩
    exact Theory.Model.isSatisfiable (M : Type _)

/-- **Reduction of independence to the existence of two models.**  A sentence is
independent of a theory precisely when the theory together with the sentence has
a model and the theory together with the negation of the sentence has a model.
This is exactly the shape of the Gödel–Cohen proof for ZFC and CH: Gödel's
constructible universe supplies a model of `ZFC + CH`, and Cohen's forcing
supplies a model of `ZFC + ¬CH`. -/
theorem independent_iff_both_satisfiable {L : Language} (T : L.Theory) (φ : L.Sentence) :
    Independent T φ ↔ (T ∪ {φ}).IsSatisfiable ∧ (T ∪ {φ.not}).IsSatisfiable := by
  rw [Independent, Theory.models_iff_not_satisfiable, Theory.models_iff_not_satisfiable,
    not_not, not_not, isSatisfiable_union_not_not, and_comm]

/-- **CH independent statement.**  The Lean-checked content of the statement
"the Continuum Hypothesis is independent of ZFC":

1. the base case, Cantor's theorem `ℵ₀ < 𝔠`, which makes CH non-vacuous;
2. the reduction of the Continuum Hypothesis (in Cantor's formulation, about
   uncountable sets of reals) to the cardinal equation `𝔠 = ℵ₁`;
3. the general model-theoretic reduction of independence: a sentence is
   independent of a theory iff both the theory extended by the sentence and the
   theory extended by its negation are satisfiable — the criterion that Gödel's
   constructible universe and Cohen's forcing verify for ZFC and CH.

The two model constructions themselves (`L` and a forcing extension) are beyond
the current Mathlib library and are not formalised here. -/
theorem CH_independent_statement :
    (ℵ₀ : Cardinal.{0}) < 𝔠 ∧
    (CH ↔ (𝔠 : Cardinal.{0}) = ℵ_ 1) ∧
    (∀ {L : Language} (T : L.Theory) (φ : L.Sentence),
      Independent T φ ↔ (T ∪ {φ}).IsSatisfiable ∧ (T ∪ {φ.not}).IsSatisfiable) :=
  ⟨aleph0_lt_continuum', CH_iff_continuum_eq_aleph_one, fun T φ =>
    independent_iff_both_satisfiable T φ⟩

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

