import Mathlib

namespace Brockian.OddPerfectThreePrimes

open Finset

/-- A geometric-sum identity: `(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/

lemma three_le_of_mem_primeFactors {n p : ℕ} (ho : Odd n) (hp : p ∈ n.primeFactors) :
    3 ≤ p := by
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hp_odd : Odd p := ho.of_dvd_nat hp_dvd
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_ge_two : 2 ≤ p := Nat.Prime.two_le hp_prime
  obtain ⟨k, hk⟩ := hp_odd
  omega

/-- An odd number whose set of prime factors is a pair `{p, q}` is deficient. -/
