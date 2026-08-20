import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


def MOD (p n : ℕ) (x : ℕ → Bool) : Bool := decide (popCount n x % p = 0)

/-- The circuit `C` computes the Boolean function `f` of the first `n` variables. -/
