import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem Deg_finrank_le (F : Type*) [Field F] (n d : ℕ) :
    Module.finrank F (Deg F n d) ≤ ∑ i ∈ range (d + 1), n.choose i := by
  classical
  have hset : {f : (Fin n → Bool) → F | ∃ S : Finset (Fin n), S.card ≤ d ∧ f = mono F S}
      = ↑((Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ d)).image (mono F)) := by
    ext f
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, mem_filter,
      mem_univ, true_and]
    constructor
    · rintro ⟨S, hS, rfl⟩; exact ⟨S, hS, rfl⟩
    · rintro ⟨S, hS, rfl⟩; exact ⟨S, hS, rfl⟩
  have hd : Deg F n d = Submodule.span F
      (↑((Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ d)).image (mono F)) :
        Set ((Fin n → Bool) → F)) := by
    rw [Deg, hset]
  rw [hd]
  refine le_trans (finrank_span_le_card _) ?_
  rw [← card_filter_card_le n d, Finset.toFinset_coe]
  exact Finset.card_image_le

/-- Key counting consequence: if every function on the cube agrees on `A` with some function
of degree at most `d`, then `A` is small. -/
