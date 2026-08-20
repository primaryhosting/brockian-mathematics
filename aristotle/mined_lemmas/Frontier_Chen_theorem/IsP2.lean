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

def IsP2 (q : ℕ) : Prop := 1 ≤ Omega q ∧ Omega q ≤ 2

/-- `IsChenNumber n` says that `n` can be written as `p + q` with `p` prime and `q`
a prime or a product of two primes.  Chen's theorem asserts that every sufficiently
large even number is a Chen number. -/
