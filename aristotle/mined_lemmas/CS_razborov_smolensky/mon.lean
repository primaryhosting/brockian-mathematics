import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


def mon {n : ℕ} (S : Finset (Fin n)) : Cube n → F := fun x => ∏ i ∈ S, bitv F (x i)

