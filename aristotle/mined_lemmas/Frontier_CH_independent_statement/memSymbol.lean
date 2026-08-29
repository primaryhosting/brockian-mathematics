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

def memSymbol : setTheoryLang.Relations 2 := (by exact () : Unit)

/-- A sentence `φ` is independent of a theory `T` when neither `φ` nor `¬ φ` is a consequence
of `T`. -/
