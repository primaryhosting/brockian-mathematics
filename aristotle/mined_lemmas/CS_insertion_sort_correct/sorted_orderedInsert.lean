/-
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Insertion Sort Correct

A self-contained development of insertion sort and its correctness proof.
-/

namespace CS

variable {α : Type*} (r : α → α → Prop) [DecidableRel r]

/-- Insert `a` into the list `l`, assumed sorted with respect to `r`. -/

theorem sorted_orderedInsert (a : α) :
    ∀ l : List α, List.Pairwise r l → List.Pairwise r (orderedInsert r a l)
  | [], _ => by simp
  | b :: l, hl => by
    rw [orderedInsert_cons]
    rcases List.pairwise_cons.1 hl with ⟨hb, hl'⟩
    by_cases h : r a b
    · rw [if_pos h]
      refine List.pairwise_cons.2 ⟨?_, hl⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h
      · exact _root_.trans h (hb c hc)
    · rw [if_neg h]
      refine List.pairwise_cons.2 ⟨?_, sorted_orderedInsert a l hl'⟩
      intro c hc
      have hmem : c ∈ a :: l :=
        (perm_orderedInsert r a l).mem_iff.1 hc
      rcases List.mem_cons.1 hmem with rfl | hc'
      · exact (Std.Total.total (r := r) _ b).resolve_left h
      · exact hb c hc'

/-- Insertion sort produces a sorted (pairwise-`r`) list. -/
