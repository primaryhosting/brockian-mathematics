import Mathlib
namespace Brockian.OddPerfectThreePrimes
/-- An odd perfect number has at least three distinct prime factors. Prove; axiom-clean, no sorry. -/
theorem oddPerfect_three_primes {n : ℕ} (ho : Odd n) (hp : Nat.Perfect n) :
    3 ≤ n.primeFactors.card := by
  sorry
end Brockian.OddPerfectThreePrimes
