import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/

lemma exists_free_color (T : Finset V) (g : V → Fin 5) (hT : T.card ≤ 4) :
    ∃ f : Fin 5, ∀ y ∈ T, g y ≠ f := by
  have h1 : (T.image g).card ≤ 4 := le_trans Finset.card_image_le hT
  have : ∃ f : Fin 5, f ∉ T.image g := by
    by_contra hcon
    push_neg at hcon
    have : (Finset.univ : Finset (Fin 5)) ⊆ T.image g := fun x _ => hcon x
    have := Finset.card_le_card this
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨f, hf⟩ := this
  exact ⟨f, fun y hy hgy => hf (Finset.mem_image.2 ⟨y, hy, hgy⟩)⟩

/-- The heart of the five colour theorem: a graph satisfying the reduction hypothesis coming
from planarity is `5`-colourable.  The proof is by induction on the number of vertices, using
the classical contraction argument of Kempe/Wernicke. -/
