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

def GoldbachConjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

set_option maxRecDepth 10000 in
/-- Base case, verified by kernel computation: every even `n` with `4 ≤ n ≤ 200` is a sum of
two primes. -/
