import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- If `p` and `n - p` are both prime and `p ≤ n`, then `n` is a sum of two primes. -/

private theorem goldbach_two_primes (p n : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (n - p))
    (hpn : p ≤ n) : ∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ a + b = n :=
  ⟨p, n - p, hp, hq, by omega⟩

/-- **Goldbach wheel, `K = 2`, modulus `1051`.**
Every even natural number `n` with `4 ≤ n ≤ 1051` is a sum of two primes
(the case `K = 2`, i.e. two summands, of the Goldbach wheel family). -/
