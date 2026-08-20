import Mathlib
namespace Brockian.MsChebyshevTheta
/-- Chebyshev's upper bound: the first Chebyshev function θ(n) = ∑_{p ≤ n} log p satisfies
    θ(n) ≤ n·log 4. -/
theorem chebyshev_theta (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p ≤ n * Real.log 4 := by
  sorry
end Brockian.MsChebyshevTheta
