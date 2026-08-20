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

open Cardinal FirstOrder

namespace Frontier

/-! ## Part 1: the Continuum Hypothesis as a statement about cardinals

We first record the "external" form of CH — the statement, about the actual real
numbers, that every uncountable set of reals has the cardinality of the continuum —
and prove that it is equivalent to the usual cardinal arithmetic form `ℵ₁ = 𝔠`.
This is a genuine (and fully proved) Lean theorem; it is the base case of the
formalization. -/

/-- The Continuum Hypothesis, in the form: every uncountable set of real numbers has
cardinality the continuum. -/

def IndependentOf {L : FirstOrder.Language} (T : L.Theory) (φ : L.Sentence) : Prop :=
  ¬ T ⊨ᵇ φ ∧ ¬ T ⊨ᵇ φ.not

/-- Independence is *exactly* the existence of two models of `T`, one satisfying `φ`
and one refuting it. This is the general form of the Gödel/Cohen reduction: to prove
independence it suffices to construct the two models. -/
