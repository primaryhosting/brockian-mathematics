/-
/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
(Lean requires the `import` command to be the very first command of a file, so
the header above is reproduced verbatim inside this comment and again as the
module docstring below.)
-/
import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- The set of residue classes modulo `p` that are occupied by the shift set `H`. -/

theorem admissible_iff_small_primes (H : Finset ℤ) :
    Admissible H ↔
      ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  constructor
  · intro hH p hp _
    exact hH p hp
  · intro hH p hp
    by_cases hle : p ≤ H.card
    · exact hH p hp hle
    · push_neg at hle
      refine (exists_missed_residue_iff_card_lt hp).mpr ?_
      exact lt_of_le_of_lt (Finset.card_image_le) hle

/-- A pattern all of whose shifts avoid divisibility by every prime up to its own size
is admissible: for such primes the class `0` is missed, and larger primes are handled by
pigeonhole. -/
