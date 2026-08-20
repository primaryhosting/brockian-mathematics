/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-! ## Boolean circuits (straight-line programs) -/

/-- A single gate of a straight-line Boolean program.  Arguments refer to positions in the
current environment (first the input bits, then the values of the previously computed gates).
Out-of-range references evaluate to `false`. -/
inductive Gate
  | const (b : Bool)
  | not (a : ℕ)
  | and (a b : ℕ)
  | or (a b : ℕ)
deriving DecidableEq

/-- A Boolean circuit is a straight-line program, i.e. a list of gates. -/
abbrev Circuit := List Gate

/-- Value of a single gate in a given environment. -/

def HardnessHypothesis (M : Model) : Prop :=
  ∃ L : List Bool → Bool, M.InE L ∧ ExpCircuitHard L

/-- **Impagliazzo–Wigderson.**  Strong circuit lower bounds imply `P = BPP`.

The hypothesis `hNW` is the hardness-versus-randomness construction: from a language in `E`
of exponential circuit complexity one obtains quick pseudorandom generators (Nisan–Wigderson
generator together with hardness amplification); it is taken here as an assumption.  What is
proved here is the derandomization half of the argument in full: given the generators, the
majority vote over all seeds turns any bounded-error probabilistic polynomial-time algorithm
into an equivalent deterministic polynomial-time one, so that `BPP = P`; the converse
inclusion `P ⊆ BPP` is proved as well. -/
