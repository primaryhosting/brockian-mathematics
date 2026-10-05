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

lemma ramsey_4_3 (hsym : ∀ a b, c a b = c b a) {V : Finset α} (hV : 9 ≤ V.card) :
    (∃ S ⊆ V, S.card = 4 ∧ MonoClique c true S) ∨
      (∃ S ⊆ V, S.card = 3 ∧ MonoClique c false S) := by
  have hsym' : ∀ a b, (fun i j => !(c i j)) a b = (fun i j => !(c i j)) b a := by
    intro a b; simp only []; rw [hsym a b]
  rcases ramsey_3_4 (c := fun i j => !(c i j)) hsym' hV with ⟨S, hS, h3, hm⟩ | ⟨S, hS, h4, hm⟩
  · exact Or.inr ⟨S, hS, h3, by simpa using (monoClique_not (c := c) (x := true)).1 hm⟩
  · exact Or.inl ⟨S, hS, h4, by simpa using (monoClique_not (c := c) (x := false)).1 hm⟩

/-! ## R(4,4) ≤ 18 -/

