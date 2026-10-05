import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The statement of the Feit–Thompson (odd order) theorem: every finite group of odd
order is solvable. -/

theorem minFac_prime_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q) :
    (p * q).minFac = p := by
  have h2 := Nat.minFac_prime (n := p * q)
    (by have := hp.two_le; have := hq.two_le; nlinarith)
  have hd : (p * q).minFac ∣ p * q := Nat.minFac_dvd _
  have hle := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
  rcases (Nat.Prime.dvd_mul h2).mp hd with h3 | h3
  · exact (Nat.prime_dvd_prime_iff_eq h2 hp).mp h3
  · have := (Nat.prime_dvd_prime_iff_eq h2 hq).mp h3
    omega

/-- Base case: every finite group of order `p * q`, with `p < q` primes, is solvable.
Indeed the Sylow `q`-subgroup has index `p`, the smallest prime factor of the order, hence is
normal; it and the quotient have prime order. -/
