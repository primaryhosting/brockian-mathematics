/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- A finite set of integers `H` is *admissible* if for every prime `p` there is a residue
class mod `p` avoided by every element of `H`.  Equivalently, `H` does not cover all residues
modulo any prime; this is exactly the condition under which the singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p)/(1 - 1/p)^{|H|}` has no vanishing local factor. -/

theorem isAdmissible_iff_residueCount_lt (H : Finset ℤ) :
    IsAdmissible H ↔ ∀ p : ℕ, p.Prime → residueCount H p < p := by
  constructor
  · intro hH p hp
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨r, hr⟩ := hH p hp
    have hsub : (H.image (fun x : ℤ => (x : ZMod p))) ⊂ Finset.univ := by
      refine Finset.ssubset_univ_iff.mpr ?_
      intro hEq
      have hmem : r ∈ H.image (fun x : ℤ => (x : ZMod p)) := by simp [hEq]
      obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp hmem
      exact hr x hx hxr
    have hlt := Finset.card_lt_card hsub
    simpa [residueCount, ZMod.card p] using hlt
  · intro hH p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hcard : (H.image (fun x : ℤ => (x : ZMod p))).card < Fintype.card (ZMod p) := by
      simpa [residueCount, ZMod.card p] using hH p hp
    have hex : ∃ r : ZMod p, r ∉ H.image (fun x : ℤ => (x : ZMod p)) := by
      by_contra hc
      push_neg at hc
      have huniv : (H.image (fun x : ℤ => (x : ZMod p))) = Finset.univ :=
        Finset.eq_univ_of_forall hc
      simp [huniv] at hcard
    obtain ⟨r, hr⟩ := hex
    exact ⟨r, fun x hx hxr => hr (Finset.mem_image.mpr ⟨x, hx, hxr⟩)⟩

/-- Pigeonhole: a set with fewer than `p` elements always misses a residue mod `p`. -/
