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

lemma admissible_of_small_primes {H : Finset ℕ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → nu H p < p) : Admissible H := by
  intro p hp
  rcases Nat.lt_or_ge H.card p with hlt | hle
  · exact nu_lt_of_card_lt hlt
  · exact h p hp hle

/-- Every local factor of the singular series of an admissible tuple is positive. -/
