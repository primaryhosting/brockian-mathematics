import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/

theorem merge_pairwise (r : α → α → Prop) [DecidableRel r]
    (htotal : ∀ a b : α, r a b ∨ r b a) (htrans : ∀ a b c : α, r a b → r b c → r a c) :
    ∀ xs ys : List α, List.Pairwise r xs → List.Pairwise r ys →
      List.Pairwise r (merge r xs ys)
  | [], ys, _, hy => by rw [merge]; exact hy
  | x :: xs, [], hx, _ => by
      rw [merge]
      · exact hx
      · simp
  | x :: xs, y :: ys, hx, hy => by
      rw [List.pairwise_cons] at hx hy
      by_cases h : r x y
      · rw [merge, if_pos h, List.pairwise_cons]
        refine ⟨?_, merge_pairwise r htotal htrans xs (y :: ys) hx.2
          (List.pairwise_cons.mpr hy)⟩
        intro b hb
        rcases mem_merge.mp hb with hb | hb
        · exact hx.1 b hb
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact h
          · exact htrans x y b h (hy.1 b hb)
      · rw [merge, if_neg h, List.pairwise_cons]
        refine ⟨?_, merge_pairwise r htotal htrans (x :: xs) ys
          (List.pairwise_cons.mpr hx) hy.2⟩
        have hyx : r y x := (htotal x y).resolve_left h
        intro b hb
        rcases mem_merge.mp hb with hb | hb
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact hyx
          · exact htrans y x b hyx (hx.1 b hb)
        · exact hy.1 b hb
termination_by xs ys => xs.length + ys.length

