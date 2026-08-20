import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem count_true_eq_sum (l : List Bool) :
    l.count true = (l.map (fun b => if b = true then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases a
    · simp [ih]
    · simp [ih]; omega

