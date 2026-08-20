import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem list_count_map {α : Type*} (l : List α) (f : α → Bool) :
    (l.map f).count true = ∑ i : Fin l.length, (if f (l.get i) = true then 1 else 0) := by
  rw [count_true_eq_sum, List.map_map, list_sum_map]
  simp

/-! ### Fermat's little theorem in characteristic `q` -/

