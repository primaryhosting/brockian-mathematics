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

def ChenStatement : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ChenRepresentation n

/-- The Goldbach conjecture: every even number `≥ 4` is a sum of two primes. -/
