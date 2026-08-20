import Mathlib
/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `q` is *almost prime of order 2*: it has at most two prime factors, counted with
multiplicity (i.e. `Ω q ≤ 2`, so `q` is `1`, a prime, or a product of two primes). -/

theorem almostPrime2_of_prime {q : ℕ} (hq : q.Prime) : AlmostPrime2 q := by
  simp [AlmostPrime2, Nat.primeFactorsList_prime hq]

/-- A semiprime (product of two primes) is almost prime of order 2. -/
