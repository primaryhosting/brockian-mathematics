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

def ChenRepresentation (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ AlmostPrime2 q ∧ n = p + q

/-- **Chen's theorem** (statement): every sufficiently large even number `n` can be written
as `p + q` with `p` prime and `q` a product of at most two primes. -/
