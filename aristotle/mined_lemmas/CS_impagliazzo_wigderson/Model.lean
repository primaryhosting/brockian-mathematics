/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace CS

/-! ## Boolean strings, probabilities and majority votes -/

/-- Boolean strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The probability that the test `T` accepts a uniformly random string of length `k`. -/

def Model.BPP (M : Model) : Set Lang := {L | ∃ A, M.EffRand A ∧ A.Decides L}

/-- **Strong circuit lower bound.**  There is a language decidable in deterministic
exponential time whose characteristic functions require circuits of size `2 ^ (ε * n)`
for some `ε > 0` and all large `n`. -/
