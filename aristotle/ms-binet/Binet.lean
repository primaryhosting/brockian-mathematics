import Mathlib
namespace Brockian.MsBinet
/-- Binet's formula: Fₙ = (φⁿ − ψⁿ)/√5 with φ = (1+√5)/2, ψ = (1−√5)/2. -/
theorem binet (n : ℕ) :
    (Nat.fib n : ℝ)
      = (((1 + Real.sqrt 5) / 2) ^ n - ((1 - Real.sqrt 5) / 2) ^ n) / Real.sqrt 5 := by
  sorry
end Brockian.MsBinet
