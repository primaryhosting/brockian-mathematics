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

lemma monoClique_triple {v i j : α} (hsym : ∀ a b, c a b = c b a)
    (hvi : c v i = x) (hvj : c v j = x) (hij : c i j = x) :
    MonoClique c x ({v, i, j} : Finset α) := by
  have hiv : c i v = x := by rw [hsym]; exact hvi
  have hjv : c j v = x := by rw [hsym]; exact hvj
  have hji : c j i = x := by rw [hsym]; exact hij
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hab
      | assumption

