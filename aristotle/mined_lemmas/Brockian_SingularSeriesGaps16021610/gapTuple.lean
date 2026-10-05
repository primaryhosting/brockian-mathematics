/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number: `2 ≤ p` and the only divisors of `p` are `1` and `p`.
(This is the usual notion of a prime natural number.) -/

def gapTuple : List Nat := [0, 2, 6, 8, 12, 18, 20, 26]

/-- For primes larger than the diameter of the pattern, the residue `1` is omitted. -/
