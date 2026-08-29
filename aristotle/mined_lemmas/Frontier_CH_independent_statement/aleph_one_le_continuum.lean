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

theorem aleph_one_le_continuum : (ℵ₁ : Cardinal.{0}) ≤ 𝔠 :=
  Cardinal.aleph_one_le_continuum

/-- Cantor's theorem in the relevant instance: `ℵ₀ < 2 ^ ℵ₀ = 𝔠`. -/
