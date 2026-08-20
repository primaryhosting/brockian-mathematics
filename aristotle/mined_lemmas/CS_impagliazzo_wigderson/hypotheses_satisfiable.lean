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

theorem hypotheses_satisfiable :
    ∃ M : Model, HardnessHypothesis M ∧ DerandomizationHypothesis M := by
  refine ⟨emptyModel, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := exists_expCircuitHard
    exact ⟨L, trivial, hL⟩
  · intro m _
    exact ⟨{ G := fun _ _ => []
             s := fun _ => 0
             polyG := trivial
             polyS := trivial
             logSeed := ⟨0, fun _ => by simp⟩
             fools := fun _ h _ => absurd h (fun h => h) }⟩


end CS

