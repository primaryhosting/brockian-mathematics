import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem bitv_mul_self (b : Bool) : bitv F b * bitv F b = bitv F b := by
  cases b <;> simp

variable {F}

/-- The multilinear monomial associated with a set of coordinates. -/
