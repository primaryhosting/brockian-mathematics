import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma descend_four_pow {a x y z t : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 ^ a * t) :
    ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = t := by
  induction a generalizing x y z with
  | zero =>
      refine ⟨x, y, z, ?_⟩
      simpa using h
  | succ a ih =>
      have h' : x ^ 2 + y ^ 2 + z ^ 2 = 4 * (4 ^ a * t) := by
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
      rcases descend_four (x := x) (y := y) (z := z) (m := 4 ^ a * t) h' with ⟨x1, y1, z1, h1⟩
      exact ih (x := x1) (y := y1) (z := z1) h1

/-- If `n` is not a three-square exception, then after removing a maximal power of `4` we get a
reduced factor `t` with `t % 8 ≠ 7`. This is the mod-8 obstruction that remains after `4`-descent. -/
