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

theorem independent_of_two_models {L : Language} {T : L.Theory} {φ : L.Sentence}
    (hpos : (T ∪ {φ}).IsSatisfiable) (hneg : (T ∪ {φ.not}).IsSatisfiable) :
    Independent T φ :=
  ⟨fun hm => ((Theory.models_iff_not_satisfiable φ).1 hm) hneg,
    not_models_not_of_isSatisfiable hpos⟩

/-- A theory with an independent sentence is incomplete. -/
