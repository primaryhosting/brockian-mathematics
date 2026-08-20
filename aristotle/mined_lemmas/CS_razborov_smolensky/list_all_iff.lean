import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem list_all_iff {α : Type*} (l : List α) (f : α → Bool) :
    (l.map f).all id = true ↔ ∀ i : Fin l.length, f (l.get i) = true := by
  simp [List.all_eq_true, List.mem_iff_get]

