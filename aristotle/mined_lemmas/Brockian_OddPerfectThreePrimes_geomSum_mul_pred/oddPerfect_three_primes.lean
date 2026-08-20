import Mathlib

namespace Brockian.OddPerfectThreePrimes

open Finset

/-- A geometric-sum identity: `(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/

theorem oddPerfect_three_primes {n : ℕ} (ho : Odd n) (hp : Nat.Perfect n) :
    3 ≤ n.primeFactors.card := by
  by_contra h
  have hc : n.primeFactors.card ≤ 2 := by omega
  have hd := odd_deficient_of_primeFactors_card_le_two ho hc
  exact (Nat.deficient_iff_not_abundant_and_not_perfect hp.2.ne').mp hd |>.2 hp

end Brockian.OddPerfectThreePrimes

