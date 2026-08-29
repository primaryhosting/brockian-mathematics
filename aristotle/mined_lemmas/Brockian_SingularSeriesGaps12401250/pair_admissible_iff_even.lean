/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Key Mathlib ingredients used: `Finset.card_image_le` (a tuple occupies at most `#H`
residue classes, so only primes `p ≤ #H` can obstruct admissibility),
`ZMod.intCast_zmod_eq_zero_iff_dvd` and `even_iff_two_dvd` (the prime `2` analysis),
`Finset.prod_pos` and `zpow_pos` (positivity of the singular series).
-/

open Finset

namespace Brockian

/-- The set of residue classes modulo `p` occupied by the integer tuple `H`. -/

theorem pair_admissible_iff_even (d : ℤ) :
    Admissible ({0, d} : Finset ℤ) ↔ Even d := by
  classical
  constructor
  · intro h
    have h2 := h 2 Nat.prime_two
    rw [residues_pair] at h2
    have hd : (d : ZMod 2) = 0 := by
      by_contra hne
      have : ({0, (d : ZMod 2)} : Finset (ZMod 2)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa [eq_comm] using hne), Finset.card_singleton]
      omega
    have : (2 : ℤ) ∣ d := by
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd d 2).1 hd
    exact (even_iff_two_dvd).2 this
  · intro hd p hp
    rcases eq_or_ne p 2 with rfl | hne
    · rw [residues_pair]
      have hd0 : (d : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd d 2).2 (by exact_mod_cast (even_iff_two_dvd).1 hd)
      rw [hd0]
      simp
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hcard : (({0, d} : Finset ℤ)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      exact lt_of_le_of_lt (le_trans (card_residues_le _ _) hcard) (by omega)

/-- Each local factor of an admissible tuple is strictly positive. -/
