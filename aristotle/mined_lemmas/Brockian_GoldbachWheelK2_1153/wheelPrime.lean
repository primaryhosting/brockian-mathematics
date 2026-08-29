/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`n` is at least `2` and its only divisors are `1` and `n`. -/

def wheelPrime (n : Nat) : Bool :=
  2 ≤ n && wheelSpokes.all (fun p => n == p || n % p != 0)

/-- Every integer `q` with `2 ≤ q ≤ 36` is divisible by one of the wheel spokes. -/
