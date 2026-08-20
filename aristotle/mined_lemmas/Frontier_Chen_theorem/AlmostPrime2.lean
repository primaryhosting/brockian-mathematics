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

def AlmostPrime2 (q : ℕ) : Prop := q.primeFactorsList.length ≤ 2

instance (q : ℕ) : Decidable (AlmostPrime2 q) := by
  unfold AlmostPrime2; infer_instance

/-- The definition of `AlmostPrime2` agrees with the arithmetic function `Ω`
(`ArithmeticFunction.cardFactors`). -/
