import RequestProject.BlumTime

/-!
# The core of the speed-up construction

This file contains the (first-order, oracle-parametrised) combinatorial core of the
diagonal construction used in the proof of Blum's speed-up theorem.

The construction is parametrised by two functions:

* `rf : ℕ → ℕ`, the speed-up factor;
* `T : ℕ → ℕ`, an oracle giving the running time of the (self-referential) code under
  construction at a given input.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Small helpers -/

/-- Bounded universal quantifier, as a `Bool`. -/

theorem leastNotIn_not_mem (V : List ℕ) : leastNotIn V ∉ V := by
  have hex : ∃ v ∈ List.range (V.length + 1), (!V.contains v) = true := by
    by_contra h
    push_neg at h
    simp only [Bool.not_not_eq, List.contains_iff_mem, List.mem_range] at h
    have hsub : Finset.range (V.length + 1) ⊆ V.toFinset := by
      intro v hv
      simp only [Finset.mem_range] at hv
      simpa using h v hv
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_range] at hcard
    exact absurd (le_trans hcard (List.toFinset_card_le V)) (by omega)
  have h1 : (List.range (V.length + 1)).findIdx (fun v => !V.contains v)
      < (List.range (V.length + 1)).length := List.findIdx_lt_length.2 hex
  have h2 := List.findIdx_getElem (w := h1) (p := fun v => !V.contains v)
    (xs := List.range (V.length + 1))
  rw [List.getElem_range] at h2
  simpa [leastNotIn, List.contains_iff_mem] using h2

/-! ### The construction -/

/-- The largest running time among the members `(i+1, d)` of the family, `d ≤ y`, on input `y`. -/
