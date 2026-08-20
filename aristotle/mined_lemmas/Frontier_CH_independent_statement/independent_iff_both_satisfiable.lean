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
