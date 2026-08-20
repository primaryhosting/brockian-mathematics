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

def BoolCircuit.size {n : ℕ} : BoolCircuit n → ℕ
  | .var _ => 1
  | .const _ => 1
  | .not c => c.size + 1
  | .and c d => c.size + d.size + 1
  | .or c d => c.size + d.size + 1

/-! ## An abstract model of efficient computation -/

/-- An abstract uniform model of computation, recording which languages are decidable in
deterministic polynomial time (`Poly`), which randomized algorithms run in polynomial
time (`EffRand`), which languages are decidable in deterministic exponential time
(`ExpTime`) and which pseudorandom generators are polynomial-time computable (`EffPRG`),
together with the two closure properties that we use:

* a deterministic polynomial-time decider can be regarded as a (zero-error) randomized
  polynomial-time algorithm;
* an efficient randomized algorithm combined with an efficient logarithmic-seed generator
  can be simulated deterministically in polynomial time, by cycling through all
  (polynomially many) seeds and taking a majority vote. -/
structure Model where
  /-- the class `P` -/
  Poly : Lang → Prop
  /-- the polynomial-time randomized algorithms -/
  EffRand : RandAlg → Prop
  /-- the class `E`/`EXP` of languages decidable in deterministic exponential time -/
  ExpTime : Lang → Prop
  /-- the polynomial-time computable pseudorandom generators -/
  EffPRG : {A : RandAlg} → PRG A → Prop
  /-- `P ⊆ BPP` -/
  det_mem_rand : ∀ L, Poly L → ∃ A, EffRand A ∧ A.Decides L
  /-- exhaustive search over the polynomially many seeds is a polynomial-time algorithm -/
  derandomize_poly : ∀ (A : RandAlg) (G : PRG A), EffRand A → EffPRG G →
    Poly (derandomize A G)

/-- The class `P` of the model. -/
