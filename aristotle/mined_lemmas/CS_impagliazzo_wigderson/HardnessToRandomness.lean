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

def HardnessToRandomness (M : Model) : Prop :=
  StrongCircuitLowerBound M → ∀ A : RandAlg, M.EffRand A → ∃ G : PRG A, M.EffPRG G

/-! ## The Impagliazzo–Wigderson theorem -/

/-- **Impagliazzo–Wigderson.**  In a model of computation equipped with the
hardness-versus-randomness construction, a strong circuit lower bound (a language in
exponential time requiring circuits of size `2 ^ (ε n)`) implies `P = BPP`.

The derandomization argument itself is proved here: from the pseudorandom generator
supplied by `HardnessToRandomness` one gets, for every bounded-error randomized
polynomial-time algorithm, a deterministic algorithm which enumerates all seeds and takes
a majority vote, and this deterministic algorithm decides *exactly* the same language
(`derandomize_eq`, via the `1/6`-fooling estimate `maj_comp_eq_true`/`maj_comp_eq_false`).
The two efficiency facts used — that a deterministic algorithm is a special randomized one
and that the seed enumeration runs in polynomial time — are the closure properties
recorded in `Model`. -/
