import Mathlib
namespace Brockian.PrimesReciprocalDiverges
/-- Euler's theorem: the sum of the reciprocals of the primes diverges. -/
theorem primes_reciprocal_not_summable :
    ¬ Summable (fun p : Nat.Primes => (1 : ℝ) / (p : ℝ)) := by
  sorry
end Brockian.PrimesReciprocalDiverges
