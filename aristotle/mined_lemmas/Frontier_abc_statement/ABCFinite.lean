/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Mathlib does not state the `abc` conjecture. The closest existing material is
`UniqueFactorizationMonoid.radical` (`Mathlib/RingTheory/Radical.lean`), a general radical
of an element of a UFM, and the Mason–Stothers theorem
(`Mathlib/NumberTheory/FLT/MasonStothers.lean`), the polynomial analogue of `abc`.
Neither closes the statement below, so the radical for `ℕ` and both formulations of the
conjecture are set up here from scratch.
-/

namespace Frontier

open scoped BigOperators

/-- The radical of a natural number: the product of its distinct prime factors.
By convention `rad 0 = rad 1 = 1`. -/

def ABCFinite : Prop := ∀ ε : ℝ, 0 < ε → (abcTriples ε).Finite

/-- The `abc` conjecture, effective-constant form: for every `ε > 0` there is `K > 0` with
`c ≤ K * rad (a*b*c) ^ (1+ε)` for all coprime triples `a + b = c`. -/
