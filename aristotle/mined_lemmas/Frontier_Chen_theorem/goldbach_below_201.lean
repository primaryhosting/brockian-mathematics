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

theorem goldbach_below_201 :
    ∀ n < 201, 4 ≤ n → n % 2 = 0 → ∃ p ≤ n, ∃ q ≤ n, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  decide

/-- Base case of Chen's theorem, unconditionally: every even `n` with `4 ≤ n ≤ 200` has a
Chen representation. -/
