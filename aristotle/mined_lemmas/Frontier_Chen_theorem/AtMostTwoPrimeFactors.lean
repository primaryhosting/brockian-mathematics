/-
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `AtMostTwoPrimeFactors q` says that `q` is a product of at most two primes,
i.e. `q = 1`, or `q` is prime, or `q` is a product of two (not necessarily distinct)
primes.  Equivalently (see `atMostTwoPrimeFactors_iff_bigOmega_le_two`), the number of
prime factors of `q`, counted with multiplicity, is at most `2`.  These are the
"almost primes" `P₂` appearing in Chen's theorem. -/

def AtMostTwoPrimeFactors (q : ℕ) : Prop :=
  q = 1 ∨ q.Prime ∨ ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ q = a * b

/-- `ChenRepresentation n` says that `n` can be written as `p + q` with `p` prime and `q`
having at most two prime factors. -/
