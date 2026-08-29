/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

open Finset

/-- A finite set of integers is *admissible* if, for every prime `p`, it fails to cover
all residue classes modulo `p`.  This is exactly the condition under which the
Hardy–Littlewood singular series of the tuple is nonzero. -/

lemma exists_missing_residue (S : Finset ℤ) (p : ℕ) (hp : p.Prime) (h : S.card < p) :
    ∃ r : ZMod p, ∀ s ∈ S, (s : ZMod p) ≠ r := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set T := S.image (fun s : ℤ => (s : ZMod p)) with hT
  have hcard : T.card < Fintype.card (ZMod p) := by
    have hle : T.card ≤ S.card := Finset.card_image_le
    simpa [ZMod.card p] using lt_of_le_of_lt hle h
  obtain ⟨r, hr⟩ : ∃ r : ZMod p, r ∉ T := by
    by_contra hc
    push_neg at hc
    have hu : T = Finset.univ := Finset.eq_univ_iff_forall.mpr hc
    rw [hu, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  exact ⟨r, fun s hs hsr => hr (by rw [hT]; exact Finset.mem_image.mpr ⟨s, hs, hsr⟩)⟩

/-- A gap `d` is admissible (as the pair `{0, d}`) exactly when `d` is even and nonzero. -/
