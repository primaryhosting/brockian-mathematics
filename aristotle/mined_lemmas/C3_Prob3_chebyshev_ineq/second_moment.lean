import Mathlib
open Finset
namespace C3.Prob3

/-- Chebyshev-type inequality: `a²` times the number of indices with `a ≤ |xᵢ|`
is at most the sum of squares. -/

theorem second_moment {n : ℕ} (x : Fin n → ℝ) : (∑ i, x i)^2 ≤ n * ∑ i, (x i)^2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := x)
  simpa using h

/-- Union bound. -/
