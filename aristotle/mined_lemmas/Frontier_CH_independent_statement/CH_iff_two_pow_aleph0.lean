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

theorem CH_iff_two_pow_aleph0 : CH ↔ (2 : Cardinal.{0}) ^ (ℵ₀ : Cardinal.{0}) = ℵ₁ := by
  rw [CH, Cardinal.two_power_aleph0]

/-! ## Part 2: what independence means, and the Gödel/Cohen reduction

Lean cannot itself decide the provability of a sentence of ZFC — `Prop` here is Lean's
own logic, not ZFC's — so "CH is independent of ZFC" is formalized in the standard way,
as a statement about a first-order theory `T` and a sentence `φ` of its language:
neither `φ` nor `¬ φ` is a consequence of `T`.

The theorem below is the Lean-checked *reduction*: independence follows from the two
relative-consistency results,

* Gödel (1938): `ZFC + CH` has a model (the constructible universe `L`);
* Cohen (1963): `ZFC + ¬CH` has a model (a forcing extension),

each expressed as satisfiability of the corresponding extension of `T`.
-/

/-- `φ` is independent of the theory `T`: neither `φ` nor its negation is entailed by `T`. -/
