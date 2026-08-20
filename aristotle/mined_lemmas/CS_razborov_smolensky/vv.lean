import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


def vv (ζ : F) (i : Fin n) : Cube n → F := fun x => 1 + (ζ⁻¹ - 1) * bitv F (x i)

/-- The product `∏_{i ∈ S} ζ ^ (x i)`. -/
