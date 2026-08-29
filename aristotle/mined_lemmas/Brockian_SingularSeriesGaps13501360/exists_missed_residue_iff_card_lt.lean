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

theorem exists_missed_residue_iff_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime) :
    (∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r) ↔ (coveredResidues H p).card < p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  constructor
  · rintro ⟨r, hr⟩
    have hrn : r ∉ coveredResidues H p := by
      simp only [coveredResidues, Finset.mem_image, not_exists]
      rintro h ⟨hh, rfl⟩
      exact hr h hh rfl
    calc (coveredResidues H p).card < Finset.univ.card := by
            refine Finset.card_lt_card ?_
            refine Finset.ssubset_univ_iff.mpr ?_
            intro hcontra
            exact hrn (hcontra ▸ Finset.mem_univ r)
      _ = p := by simp [Finset.card_univ, hcard]
  · intro hlt
    by_contra hcon
    push_neg at hcon
    have huniv : coveredResidues H p = Finset.univ := by
      refine Finset.eq_univ_iff_forall.mpr ?_
      intro r
      obtain ⟨h, hh, hhr⟩ := hcon r
      simp only [coveredResidues, Finset.mem_image]
      exact ⟨h, hh, by simpa using hhr⟩
    rw [huniv] at hlt
    simp [Finset.card_univ, hcard] at hlt

/-- Pigeonhole: a set of `k` shifts can only occupy `k` residue classes, so all primes
exceeding the size of the pattern are automatically harmless.  This is the reformulation
that reduces admissibility to a *finite* check. -/
