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

lemma admissible_pair_iff (d : ℕ) : Admissible ({0, d} : Finset ℕ) ↔ Even d := by
  constructor
  · intro h
    by_contra hodd
    have h2 : d % 2 = 1 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hodd)
    have := h 2 Nat.prime_two
    rw [nu_pair, h2] at this
    simp at this
  · intro he p hp
    rcases eq_or_ne p 2 with rfl | hne
    · have h2 : d % 2 = 0 := Nat.even_iff.1 he
      rw [nu_pair, h2]
      simp
    · have h2p := hp.two_le
      have hp3 : 3 ≤ p := by omega
      refine nu_lt_of_card_lt (lt_of_le_of_lt ?_ (by omega : 2 < p))
      exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- The four-element tuple `{0, 1452, 1454, 1460}` is admissible. -/
