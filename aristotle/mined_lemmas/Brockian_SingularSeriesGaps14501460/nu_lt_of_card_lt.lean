import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- `nu H p` is the number of distinct residue classes modulo `p` occupied by the
tuple `H`; in the Hardy–Littlewood singular series this is the quantity `ν_p(H)`
appearing in the local factor `(1 - ν_p(H)/p)(1 - 1/p)^{-|H|}`. -/

lemma nu_lt_of_card_lt {H : Finset ℕ} {p : ℕ} (h : H.card < p) : nu H p < p :=
  lt_of_le_of_lt (nu_le_card H p) h

/-- Admissibility only has to be checked at the primes `p ≤ |H|`. -/
