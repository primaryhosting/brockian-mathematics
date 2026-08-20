import Mathlib
namespace Brockian.MsChebyshevSum
/-- Chebyshev's sum inequality: for similarly-sorted sequences (a monotone, b monotone the same
    way), n·∑ aᵢbᵢ ≥ (∑ aᵢ)(∑ bᵢ). -/
theorem chebyshev_sum {n : ℕ} (a b : Fin n → ℝ) (hmono : Monotone a) (hmono' : Monotone b) :
    (n : ℝ) * ∑ i, a i * b i ≥ (∑ i, a i) * (∑ i, b i) := by
  sorry
end Brockian.MsChebyshevSum
