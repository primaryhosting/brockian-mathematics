/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian

/-- Elementary primality predicate: `p` is at least `2` and its only divisors are `1` and `p`. -/

def hasRepAux (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, p =>
      if n < p then false
      else if isPrimeB p && isPrimeB (n - p) then true
      else hasRepAux n fuel (p + 1)

/-- `hasRep n` is `true` when the search finds a representation of `n` as a sum of two primes. -/
