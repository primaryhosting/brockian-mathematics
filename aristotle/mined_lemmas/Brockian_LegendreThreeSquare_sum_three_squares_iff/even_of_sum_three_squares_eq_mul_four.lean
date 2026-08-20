import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma even_of_sum_three_squares_eq_mul_four {x y z m : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 * m) : Even x ∧ Even y ∧ Even z := by
  -- If any variable is odd, reduce mod 4 and contradict the finite check in `ZMod 4`.
  have hx : Even x := by
    rcases Nat.even_or_odd x with hx | hx
    · exact hx
    · have hx1 : ((x : ZMod 4) ^ 2) = 1 := zmod4_sq_eq_one_of_odd x hx
      have hcast := congrArg (fun n : ℕ => (n : ZMod 4)) h
      -- In `ZMod 4`, `4*m = 0`.
      have h0 : ((x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
      have : (1 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        -- replace `x^2` by `1`
        simpa [hx1, add_assoc, add_left_comm, add_comm] using h0
      exact False.elim ((zmod4_one_add_sq_add_sq_ne0 (y := (y : ZMod 4)) (z := (z : ZMod 4))) this)
  have hy : Even y := by
    rcases Nat.even_or_odd y with hy | hy
    · exact hy
    · have hy1 : ((y : ZMod 4) ^ 2) = 1 := zmod4_sq_eq_one_of_odd y hy
      have hcast := congrArg (fun n : ℕ => (n : ZMod 4)) (by
        simpa [add_assoc, add_left_comm, add_comm] using h)
      have h0 : ((y : ZMod 4) ^ 2 + (x : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
      have : (1 + (x : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        simpa [hy1, add_assoc, add_left_comm, add_comm] using h0
      exact False.elim ((zmod4_one_add_sq_add_sq_ne0 (y := (x : ZMod 4)) (z := (z : ZMod 4))) this)
  have hz : Even z := by
    rcases Nat.even_or_odd z with hz | hz
    · exact hz
    · have hz1 : ((z : ZMod 4) ^ 2) = 1 := zmod4_sq_eq_one_of_odd z hz
      have hcast := congrArg (fun n : ℕ => (n : ZMod 4)) (by
        simpa [add_assoc, add_left_comm, add_comm] using h)
      have h0 : ((z : ZMod 4) ^ 2 + (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2) = 0 := by
        simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
      have : (1 + (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2) = 0 := by
        simpa [hz1, add_assoc, add_left_comm, add_comm] using h0
      exact False.elim ((zmod4_one_add_sq_add_sq_ne0 (y := (x : ZMod 4)) (z := (y : ZMod 4))) this)
  exact ⟨hx, hy, hz⟩

