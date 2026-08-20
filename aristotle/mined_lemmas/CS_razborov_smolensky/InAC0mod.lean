import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

def InAC0mod (q : ℕ) (f : ∀ n, Cube n → Bool) : Prop :=
  ∃ d c : ℕ, ∀ n : ℕ, ∃ (k : ℕ) (C : Ckt n k) (o : Fin k),
    k ≤ c * (n + 1) ^ c ∧ C.depth o ≤ d ∧ ∀ x, C.eval q x o = f n x

/-- The `MOD p` function: `true` iff the number of ones of the input is divisible by `p`. -/
