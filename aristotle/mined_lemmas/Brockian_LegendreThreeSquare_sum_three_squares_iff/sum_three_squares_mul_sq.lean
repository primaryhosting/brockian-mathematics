import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma sum_three_squares_mul_sq (s m : ℕ)
    (hm : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = m) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = s ^ 2 * m := by
  rcases hm with ⟨x, y, z, hxyz⟩
  refine ⟨s * x, s * y, s * z, ?_⟩
  -- Expand squares and factor `s^2`.
  have hxy :
      s ^ 2 * x ^ 2 + s ^ 2 * y ^ 2 = s ^ 2 * (x ^ 2 + y ^ 2) := by
    simp [Nat.mul_add]
  have hxyz' :
      s ^ 2 * (x ^ 2 + y ^ 2) + s ^ 2 * z ^ 2 = s ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    simp [Nat.add_assoc, Nat.mul_add]
  calc
    (s * x) ^ 2 + (s * y) ^ 2 + (s * z) ^ 2
        = s ^ 2 * x ^ 2 + s ^ 2 * y ^ 2 + s ^ 2 * z ^ 2 := by
            simp [pow_two, Nat.mul_left_comm, Nat.mul_comm]
    _ = s ^ 2 * (x ^ 2 + y ^ 2) + s ^ 2 * z ^ 2 := by
            -- fold the first two terms into `s^2 * (x^2 + y^2)`
            simp [hxy]
    _ = s ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := hxyz'
    _ = s ^ 2 * m := by simp [hxyz]

end GeometryOfNumbers
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import GeometryOfNumbers.Legendre.Exceptions
import GeometryOfNumbers.Legendre.AnkenyLemmas
import GeometryOfNumbers.Legendre.Ankeny

namespace GeometryOfNumbers
open scoped NumberTheorySymbols

/-!
## Reduced residue classes for Legendre (local lemma boundaries)

At the point where `sum_three_squares_of_not_exception` reaches the “reduced” integer `t`,
we know `4 ∤ t` and `t % 8 ∈ {1,2,5,6}`.

We keep *named lemma boundaries* so:
- `GeometryOfNumbers/Legendre/Main.lean` stays readable, and
- alternative proof routes (especially the Q₁ route for `t % 8 = 5`) have a stable place to live.
-/

