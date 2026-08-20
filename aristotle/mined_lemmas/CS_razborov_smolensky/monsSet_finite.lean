import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem monsSet_finite (n d : ℕ) : (monsSet F n d).Finite :=
  Set.Finite.image _ (Set.toFinite _)

/-- Functions on the cube computed by polynomials of degree at most `d`. -/
