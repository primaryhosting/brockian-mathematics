import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem one_le_size (c : Circuit) : 1 ≤ c.size := by
  cases c <;> simp

end Circuit

/-- `x` only uses the first `n` input variables. -/
