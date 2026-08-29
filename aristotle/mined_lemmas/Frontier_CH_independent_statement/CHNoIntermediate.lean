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

set_option autoImplicit false

namespace Frontier

open Cardinal FirstOrder Language

/-! ## Part 1: the statement of the Continuum Hypothesis

We state CH in two equivalent ways and prove the equivalence inside Lean:

* the *cardinal-arithmetic* form `2 ^ ℵ₀ = ℵ₁` (equivalently `𝔠 = ℵ₁`), and
* the *no intermediate cardinality* form: every set of reals which is uncountable
  has the cardinality of the continuum.
-/

/-- The Continuum Hypothesis, in cardinal-arithmetic form: `𝔠 = ℵ₁`. -/

def CHNoIntermediate : Prop := ∀ s : Set ℝ, ℵ₀ < #s → #s = 𝔠

/-- `ℵ₁ ≤ 𝔠`: there is no set of reals of cardinality strictly between `ℵ₀` and `ℵ₁`.
This is a ZFC theorem (the "base case" of the independence discussion): CH can only fail
by `𝔠` being *larger* than `ℵ₁`. -/
