import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem depth_le_of_mem {cs : List Circuit} {c : Circuit} (h : c ∈ cs) :
    c.depth ≤ (cs.map depth).foldr max 0 := by
  induction cs with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · simp only [List.map_cons, List.foldr_cons]
      exact le_trans (ih h) (le_max_right _ _)

