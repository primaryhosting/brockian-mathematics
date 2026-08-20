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

theorem derandomize_eq (A : RandAlg) (G : PRG A) (L : Lang) (hA : A.Decides L) :
    derandomize A G = L := by
  funext n x
  rcases hd : L n x with _ | _
  · exact maj_comp_eq_false _ _ (G.fools n x) ((hA n x).2 hd)
  · exact maj_comp_eq_true _ _ (G.fools n x) ((hA n x).1 hd)

/-! ## Boolean circuits -/

/-- Boolean circuits (in tree form) over `n` input variables, with `¬, ∧, ∨` gates. -/
inductive BoolCircuit (n : ℕ) where
  | var : Fin n → BoolCircuit n
  | const : Bool → BoolCircuit n
  | not : BoolCircuit n → BoolCircuit n
  | and : BoolCircuit n → BoolCircuit n → BoolCircuit n
  | or : BoolCircuit n → BoolCircuit n → BoolCircuit n

/-- The Boolean function computed by a circuit. -/
