import Mathlib
import RequestProject.Paley

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-! ## Monochromatic cliques for a two-colouring -/

variable {α : Type*} [DecidableEq α] {c : α → α → Bool} {x : Bool}

/-- `S` is a monochromatic clique of colour `x` for the two-colouring `c`. -/

def MonoClique (c : α → α → Bool) (x : Bool) (S : Finset α) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = x

omit [DecidableEq α] in
