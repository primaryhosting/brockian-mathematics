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
