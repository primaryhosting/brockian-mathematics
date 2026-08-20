import Mathlib
namespace Brockian.MsGaussSum
/-- The quadratic Gauss sum has magnitude √p: for an odd prime p,
    |∑_{k ∈ ℤ/p} exp(2πi k²/p)|² = p. -/
theorem gauss_sum_abs_sq (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    Complex.abs (∑ k : ZMod p,
      Complex.exp (2 * Real.pi * Complex.I * ((k.val : ℂ) ^ 2) / (p : ℂ))) ^ 2 = (p : ℝ) := by
  sorry
end Brockian.MsGaussSum
