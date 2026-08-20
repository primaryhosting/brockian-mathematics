import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


def monsSet (n d : ℕ) : Set (Cube n → F) := (fun S => (mon S : Cube n → F)) '' {S | S.card ≤ d}

