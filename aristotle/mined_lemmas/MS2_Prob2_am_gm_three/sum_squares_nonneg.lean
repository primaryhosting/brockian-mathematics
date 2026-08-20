import Mathlib
open Finset
namespace MS2.Prob2

/-- AM–GM for three nonnegative reals. -/

theorem sum_squares_nonneg {n : ℕ} (a : Fin n → ℝ) : 0 ≤ ∑ i, (a i)^2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg (a i)

/-- The triangle inequality for finite sums. -/
