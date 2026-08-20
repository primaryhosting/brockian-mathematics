import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `Omega n` is the number of prime factors of `n`, counted with multiplicity
(the classical arithmetic function `Ω`). -/

def Omega (n : ℕ) : ℕ := n.primeFactorsList.length

/-- `IsP2 q` says that `q` is a *almost prime of order 2*, i.e. `q` is either a prime
or a product of two primes: it has at least one and at most two prime factors,
counted with multiplicity. -/
