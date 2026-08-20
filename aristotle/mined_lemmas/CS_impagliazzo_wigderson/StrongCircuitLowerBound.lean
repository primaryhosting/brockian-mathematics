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

def StrongCircuitLowerBound (M : Model) : Prop :=
  ∃ L : Lang, M.ExpTime L ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ c : BoolCircuit n,
    (∀ x, c.eval x = L n x) → (2 : ℝ) ^ (ε * n) ≤ (c.size : ℝ)

/-- **Hardness versus randomness.**  The Nisan–Wigderson / Impagliazzo–Wigderson
construction: a strong circuit lower bound yields, for every efficient randomized
algorithm, an efficient pseudorandom generator with logarithmic seed length fooling it. -/
