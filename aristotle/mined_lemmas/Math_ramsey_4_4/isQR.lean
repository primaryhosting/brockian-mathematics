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

def isQR (n : ℕ) : Bool :=
  n == 1 || n == 2 || n == 4 || n == 8 || n == 9 || n == 13 || n == 15 || n == 16

/-- The Paley two-colouring of the complete graph on 17 vertices. -/
