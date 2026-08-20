import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-- The *Goldbach wheel condition of order 2* for a modulus `m`:
every even number `n` is congruent, modulo `m`, to a sum `a + b` of two natural numbers
that are both coprime to `m`.

This is the condition saying that the "wheel" of modulus `m` does not obstruct
Goldbach-type representations of even numbers as sums of two numbers coprime to `m`
(in particular, as sums of two primes not dividing `m`). -/

theorem coprime_of_no_common_prime {a m : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ∣ m → ¬ p ∣ a) : Nat.Coprime a m := by
  by_contra hc
  obtain ⟨p, pp, hp⟩ := Nat.exists_prime_and_dvd hc
  exact h p pp (hp.trans (Nat.gcd_dvd_right a m)) (hp.trans (Nat.gcd_dvd_left a m))

/-- Every positive modulus satisfies the Goldbach wheel condition of order 2.

The witness is built by the Chinese remainder theorem: writing `n = k + 1` with `k` odd,
one takes `a ≡ 1` modulo every prime factor of `m` not dividing `k`, and `a ≡ 2` modulo
every prime factor of `m` dividing `k` (all such primes are odd), and then `b ≡ n - a`. -/
