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

def noDivFrom (n : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, d => if n < d * d then true else if n % d == 0 then false else noDivFrom n fuel (d + 1)

/-- Boolean primality test by trial division up to the square root. -/
