import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma coord_eq_mono (i : Fin n) : coord F i = mono F {i} := by
  funext x; simp [mono, coord]

/-- The submodule of functions of degree at most `D`. -/
