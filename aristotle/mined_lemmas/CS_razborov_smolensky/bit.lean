import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

def bit (q : ℕ) (b : Bool) : ZMod q := if b then 1 else 0

/-- `Ez z = z ^ (q-1)` is the indicator of `z ≠ 0`. -/
