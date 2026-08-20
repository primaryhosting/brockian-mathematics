import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


def popCount (n : ℕ) (x : ℕ → Bool) : ℕ := ((Finset.range n).filter (fun i => x i = true)).card

/-- The `MOD p` function on `n` variables: `true` iff the number of ones is divisible by `p`. -/
