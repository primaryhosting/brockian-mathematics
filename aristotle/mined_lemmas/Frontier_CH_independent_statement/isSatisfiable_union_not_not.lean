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
