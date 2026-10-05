/-!
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace CS

/-- `orderedInsert r a l` inserts `a` into `l` in front of the first element
`b` of `l` with `r a b`. -/

theorem sorted_orderedInsert (htotal : ∀ x y : α, r x y ∨ r y x)
    (htrans : ∀ x y z : α, r x y → r y z → r x z) (a : α) :
    ∀ l : List α, Sorted r l → Sorted r (orderedInsert r a l)
  | [], _ => List.pairwise_singleton r a
  | b :: l, hl => by
      obtain ⟨hb, hls⟩ := List.pairwise_cons.mp hl
      rw [orderedInsert_cons]
      split
      · rename_i hab
        refine List.pairwise_cons.mpr ⟨?_, ?_⟩
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hab
          · exact htrans _ _ _ hab (hb c hc)
        · exact List.pairwise_cons.mpr ⟨hb, hls⟩
      · rename_i hab
        have hba : r b a := (htotal a b).resolve_left hab
        refine List.pairwise_cons.mpr ⟨?_, sorted_orderedInsert htotal htrans a l hls⟩
        intro c hc
        rcases (mem_orderedInsert r).mp hc with rfl | hc
        · exact hba
        · exact hb c hc

/-- `insertionSort` returns a permutation of its input. -/
