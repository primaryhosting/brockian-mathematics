import Mathlib
import RequestProject.Main

/-!
# Insertion sort correctness, stated with Mathlib's `List.Sorted`

`RequestProject/Main.lean` contains the target theorem `CS.insertion_sort_correct`
(it cannot contain an `import` line, since the mandated header comment must be the
first command of the file).  Here we restate it in Mathlib vocabulary, for a
`LinearOrder`, using `List.Pairwise (· ≤ ·)` (which is Mathlib's `List.Sorted (· ≤ ·)`).
-/

set_option autoImplicit false

namespace CS

variable {α : Type*} [LinearOrder α]

/-- **Insertion sort is correct** (Mathlib phrasing): over a linear order,
`CS.insertionSort (· ≤ ·) l` is sorted (pairwise `≤`) and is a permutation of `l`. -/

theorem pairwise_orderedInsert (htotal : ∀ a b : α, le a b ∨ le b a)
    (htrans : ∀ a b c : α, le a b → le b c → le a c) (a : α) :
    ∀ l : List α, l.Pairwise le → (orderedInsert le a l).Pairwise le
  | [], _ => List.pairwise_singleton le a
  | b :: l, hl => by
    rw [List.pairwise_cons] at hl
    by_cases h : le a b
    · rw [orderedInsert_cons, if_pos h, List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.2 hl⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h
      · exact htrans _ _ _ h (hl.1 c hc)
    · rw [orderedInsert_cons, if_neg h, List.pairwise_cons]
      refine ⟨?_, pairwise_orderedInsert htotal htrans a l hl.2⟩
      intro c hc
      have hc' := (perm_orderedInsert le a l).mem_iff.1 hc
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact (htotal _ _).resolve_left h
      · exact hl.1 c hc'

/-- `insertionSort` returns a permutation of its input. -/
