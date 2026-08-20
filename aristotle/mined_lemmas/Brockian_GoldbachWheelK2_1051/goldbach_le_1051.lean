/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Brockian

/-- The wheel modulus of this member of the `GoldbachWheelK2` family. -/

theorem goldbach_le_1051 (n : Nat) (hev : n % 2 = 0) (h4 : 4 ≤ n) (hle : n ≤ 1051) :
    ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n := by
  obtain ⟨k, hk, hkn⟩ : ∃ k, k < 524 ∧ n = 2 * k + 4 := ⟨(n - 4) / 2, by omega, by omega⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := wheel_pair_core k (List.mem_range.mpr hk)
  exact ⟨p, q, wheelPrimes_prime p hp, wheelPrimes_prime q hq, by omega⟩

/-- Any nonzero residue below the (prime) wheel modulus is coprime to it. -/
