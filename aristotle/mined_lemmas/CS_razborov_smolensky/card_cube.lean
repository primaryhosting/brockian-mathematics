import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem card_cube (n : ℕ) : #(univ : Finset (Cube n)) = 2 ^ n := by
  simp [Finset.card_univ]

