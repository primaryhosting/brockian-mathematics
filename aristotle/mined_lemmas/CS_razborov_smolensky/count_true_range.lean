import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem count_true_range (x : ℕ → Bool) (n : ℕ) :
    ((List.range n).map x).count true = popCount n x := by
  induction n with
  | zero => simp [popCount]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih]
    unfold popCount
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : x n = true
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      simp [h]
    · rw [if_neg h]
      simp [h]

/-- `MOD q` itself is in `AC⁰[q]` (a single `MOD q` gate computes it); in particular the class
`AC⁰[q]` is not empty and the definitions above are not vacuous. -/
