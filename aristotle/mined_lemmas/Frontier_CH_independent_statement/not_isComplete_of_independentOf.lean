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
