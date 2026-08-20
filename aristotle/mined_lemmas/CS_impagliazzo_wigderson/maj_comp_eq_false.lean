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

theorem maj_comp_eq_false {k l : ℕ} (T : Bits k → Bool) (G : Bits l → Bits k)
    (h : |prob T - prob (fun s => T (G s))| < 1 / 6) (hT : prob T ≤ 1 / 3) :
    maj (fun s => T (G s)) = false := by
  rw [abs_sub_lt_iff] at h
  have h2 := h.2
  simp only [maj, decide_eq_false_iff_not, not_lt]
  linarith

/-! ## Languages, randomized algorithms and pseudorandom generators -/

/-- A language: for every input length, a predicate on binary strings of that length. -/
abbrev Lang := (n : ℕ) → Bits n → Bool

/-- A family of randomized algorithms: on inputs of length `n` the algorithm tosses
`len n` coins. -/
structure RandAlg where
  /-- number of random bits used on inputs of length `n` -/
  len : ℕ → ℕ
  /-- the output of the algorithm on a given input and a given random string -/
  run : (n : ℕ) → Bits n → Bits (len n) → Bool

/-- `A` decides `L` with two-sided bounded error `1/3` (the `BPP` acceptance condition). -/
