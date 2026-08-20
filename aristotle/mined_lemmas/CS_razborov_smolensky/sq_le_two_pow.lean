import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma sq_le_two_pow {u : ℕ} (hu : 4 ≤ u) : u ^ 2 ≤ 2 ^ u := by
  induction u with
  | zero => omega
  | succ v ih =>
      rcases Nat.lt_or_ge v 4 with hv | hv
      · interval_cases v <;> simp_all
      · have h1 : v ^ 2 ≤ 2 ^ v := ih (by omega)
        have h2 : 2 * v + 1 ≤ v ^ 2 := by nlinarith
        have : (v + 1) ^ 2 = v ^ 2 + (2 * v + 1) := by ring
        calc (v + 1) ^ 2 = v ^ 2 + (2 * v + 1) := this
          _ ≤ 2 ^ v + 2 ^ v := Nat.add_le_add h1 (le_trans h2 h1)
          _ = 2 ^ (v + 1) := by ring

/-- Exponentials beat polynomials: there are arbitrarily large `t` with `K * t ^ e ≤ 2 ^ t`. -/
