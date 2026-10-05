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

lemma monoClique_insert {S : Finset α} {v : α} (hsym : ∀ a b, c a b = c b a)
    (hS : MonoClique c x S) (hv : ∀ u ∈ S, c v u = x) :
    MonoClique c x (insert v S) := by
  intro a ha b hb hab
  simp only [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact hv b hb
  · rcases hb with rfl | hb
    · rw [hsym]; exact hv a ha
    · exact hS a ha b hb hab

/-! ## Neighbourhoods -/

/-- The vertices of `V` joined to `v` by colour `true`. -/
