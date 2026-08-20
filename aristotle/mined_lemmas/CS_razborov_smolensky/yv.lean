import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

noncomputable def yv (ζ : F) (i : Fin n) : Cube n → F := fun x => 1 + (ζ - 1) * coord F i x

variable (F) in
/-- The inverse of `y i`, again an affine function of `x i`. -/
