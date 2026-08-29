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

def Admissible (H : List Nat) : Prop :=
  ∀ p : Nat, NatPrime p → ∃ r, r < p ∧ ∀ h ∈ H, h % p ≠ r

/-- A number with a divisor other than `1` and itself is not prime. -/
