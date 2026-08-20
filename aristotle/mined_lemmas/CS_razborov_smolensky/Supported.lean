import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


def Supported (n : ℕ) (x : ℕ → Bool) : Prop := ∀ i, n ≤ i → x i = false

/-- The number of `true` coordinates of `x` among the first `n`. -/
