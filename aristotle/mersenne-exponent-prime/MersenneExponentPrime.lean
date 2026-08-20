import Mathlib
namespace Brockian.MersenneExponentPrime
/-- If 2^n - 1 is prime then n is prime. Prove; axiom-clean, no sorry. -/
theorem mersenne_exponent_prime {n : ℕ} (h : (2 ^ n - 1).Prime) : n.Prime := by
  sorry
end Brockian.MersenneExponentPrime
