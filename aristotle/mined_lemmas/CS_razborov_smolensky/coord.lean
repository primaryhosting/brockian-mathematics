import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

def coord {n : ℕ} (i : Fin n) : Cube n → F := fun x => if x i then 1 else 0

/-- The monomial function attached to a set `S` of coordinates. -/
