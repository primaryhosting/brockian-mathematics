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

theorem almostPrime2_iff_cardFactors (q : ℕ) :
    AlmostPrime2 q ↔ ArithmeticFunction.cardFactors q ≤ 2 := by
  simp [AlmostPrime2, ArithmeticFunction.cardFactors_apply]

/-- `1` has no prime factors. -/
