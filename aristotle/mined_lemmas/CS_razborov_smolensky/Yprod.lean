import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

noncomputable def Yprod (ζ : F) (S : Finset (Fin n)) : Cube n → F := ∏ i ∈ S, yv F ζ i

