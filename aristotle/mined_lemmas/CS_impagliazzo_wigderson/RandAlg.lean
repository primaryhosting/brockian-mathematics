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

def RandAlg.Decides (A : RandAlg) (L : Lang) : Prop :=
  ∀ (n : ℕ) (x : Bits n),
    (L n x = true → 2 / 3 ≤ prob (A.run n x)) ∧
    (L n x = false → prob (A.run n x) ≤ 1 / 3)

/-- A pseudorandom generator with logarithmic seed length that fools all the tests
arising from the randomized algorithm `A` (one test for each input). -/
structure PRG (A : RandAlg) where
  /-- seed length used on inputs of length `n` -/
  seedLen : ℕ → ℕ
  /-- the generator stretches a seed to a full random string -/
  gen : (n : ℕ) → Bits (seedLen n) → Bits (A.len n)
  /-- the seed length is logarithmic in the input length -/
  seedLen_log : ∃ c : ℕ, ∀ n, seedLen n ≤ c * Nat.log 2 (n + 1) + c
  /-- the generator fools every test of the algorithm to within `1/6` -/
  fools : ∀ (n : ℕ) (x : Bits n),
    |prob (A.run n x) - prob (fun s => A.run n x (gen n s))| < 1 / 6

/-- The deterministic language obtained by running `A` on all pseudorandom strings
produced by `G` and taking the majority vote. -/
