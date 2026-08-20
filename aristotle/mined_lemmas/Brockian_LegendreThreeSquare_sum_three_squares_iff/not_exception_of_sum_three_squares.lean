import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem not_exception_of_sum_three_squares (n : ℕ) (h : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) :
    ¬ is_three_square_exception n := by
  rcases h with ⟨x, y, z, hxyz⟩
  intro hex
  rcases hex with ⟨a, k, hn⟩
  -- descend `4^a` to get a representation of `8*k+7`
  have hdesc : ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = 8 * k + 7 := by
    refine descend_four_pow (a := a) (x := x) (y := y) (z := z) (t := 8 * k + 7) ?_
    simp [hn, hxyz]
  rcases hdesc with ⟨x', y', z', h'⟩
  -- reduce mod 8 and contradict the finite check in `ZMod 8`
  have hcast := congrArg (fun n : ℕ => (n : ZMod 8)) h'
  have : ((x' : ZMod 8) ^ 2 + (y' : ZMod 8) ^ 2 + (z' : ZMod 8) ^ 2) = (7 : ZMod 8) := by
    -- `8*k` vanishes in `ZMod 8`.
    simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
  exact (zmod8_sum_three_sq_ne7 (x := (x' : ZMod 8)) (y := (y' : ZMod 8)) (z := (z' : ZMod 8))) this

/-- Sufficient condition: n not an exception implies representation as a sum of three squares. -/
