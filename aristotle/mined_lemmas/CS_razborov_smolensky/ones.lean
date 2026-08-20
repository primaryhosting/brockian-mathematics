import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

def ones {n : ℕ} (x : Cube n) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

section Ring

variable (F : Type*) [CommRing F] {n : ℕ}

/-- The `i`-th coordinate function, valued in `F`. -/
