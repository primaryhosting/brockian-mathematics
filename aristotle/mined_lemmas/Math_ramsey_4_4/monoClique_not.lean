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

lemma monoClique_not {S : Finset α} :
    MonoClique (fun i j => !(c i j)) x S ↔ MonoClique c (!x) S := by
  constructor
  · intro h i hi j hj hij
    have h' : (!(c i j)) = x := h i hi j hj hij
    rw [← h', Bool.not_not]
  · intro h i hi j hj hij
    have h' : c i j = !x := h i hi j hj hij
    show (!(c i j)) = x
    rw [h', Bool.not_not]

