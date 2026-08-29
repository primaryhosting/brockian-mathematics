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

theorem not_natPrime_of_dvd {p a : Nat} (ha1 : a ≠ 1) (hap : a ≠ p) (h : a ∣ p) :
    ¬ NatPrime p := by
  intro hp
  rcases hp.2 a h with h1 | h2
  · exact ha1 h1
  · exact hap h2

/-- The eight-element gap pattern of diameter `26`. -/
