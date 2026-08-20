import Mathlib

namespace Brockian.OddPerfectThreePrimes

open Finset

/-- A geometric-sum identity: `(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/

lemma prime_pair_bound {p q : ℕ} (hp : 3 ≤ p) (hq : 5 ≤ q) :
    p * q ≤ 2 * ((p - 1) * (q - 1)) := by
  have hp1 : p - 1 + 1 = p := by omega
  have hq1 : q - 1 + 1 = q := by omega
  calc p * q = (p - 1 + 1) * (q - 1 + 1) := by rw [hp1, hq1]
    _ = (p - 1) * (q - 1) + (p - 1) + (q - 1) + 1 := by ring
    _ ≤ (p - 1) * (q - 1) + (p - 1) * (q - 1) := by nlinarith
    _ = 2 * ((p - 1) * (q - 1)) := by ring

/-- A number of the shape `p ^ a * q ^ b` with `p ≥ 3`, `q ≥ 5` distinct primes has
sum of divisors less than twice itself. -/
