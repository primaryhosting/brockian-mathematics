import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma final_arith {X Y P : ℕ} (h1 : 4 * P ≤ X) (h2 : 3 * Y < 2 * X)
    (h3 : 2 * X ≤ X + Y + P) : False := by omega

/-- Counting subsets of `Fin n` of size at most `D`. -/
