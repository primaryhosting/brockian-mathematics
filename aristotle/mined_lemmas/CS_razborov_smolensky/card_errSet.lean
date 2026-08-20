import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem card_errSet {n : ℕ} (P : Cube n → F) (v : Cube n → Bool) :
    #(errSet P v) = ∑ x ∈ (Finset.univ : Finset (Cube n)), if P x ≠ bitv F (v x) then 1 else 0 := by
  rw [errSet, Finset.card_filter]

/-! ### Dimension bound -/

