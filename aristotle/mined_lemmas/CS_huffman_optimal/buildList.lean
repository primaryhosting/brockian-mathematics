import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


noncomputable def buildList (w : α → ℝ) (ts : List (HTree α)) : List (HTree α) :=
  if h : 2 ≤ ts.length then
    buildList w (combineStep w ts)
  else ts
termination_by ts.length
decreasing_by
  have := combineStep_length w ts h
  omega

