import Mathlib
open Finset
namespace MS2.Combinatorics2

/-- Segner's recurrence for the Catalan numbers, stated as a sum over `range (n+1)`. -/

theorem binomial_theorem (x y : ℝ) (n : ℕ) : (x+y)^n = ∑ k ∈ range (n+1), (n.choose k) * x^k * y^(n-k) := by
  rw [add_pow]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Vandermonde's identity. -/
