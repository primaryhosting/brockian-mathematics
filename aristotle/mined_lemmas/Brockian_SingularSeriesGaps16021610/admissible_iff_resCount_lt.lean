/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- A finite set of integers `H` is *admissible* if, for every prime `p`, the elements of `H`
do not cover all residue classes modulo `p`.  Equivalently (by the Euler-product formula for
the singular series `𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}`), the singular series attached
to `H` is non-zero, so that the Hardy–Littlewood prime `k`-tuple conjecture predicts infinitely
many translates of `H` consisting entirely of primes. -/

theorem admissible_iff_resCount_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → resCount H p < p := by
  constructor
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨r, hr⟩ := hH p hp
    have hsub : H.image (fun h : ℤ => (h : ZMod p)) ⊂ Finset.univ := by
      refine Finset.ssubset_univ_iff.2 fun hEq => ?_
      have : r ∈ H.image (fun h : ℤ => (h : ZMod p)) := hEq ▸ Finset.mem_univ r
      obtain ⟨h, hh, hhr⟩ := Finset.mem_image.1 this
      exact hr h hh hhr
    have := Finset.card_lt_card hsub
    rwa [Finset.card_univ, ZMod.card] at this
  · intro hH p hp
    have hlt : (H.image (fun h : ℤ => (h : ZMod p))).card < p := hH p hp
    have hex : ∃ r : ZMod p, r ∉ H.image (fun h : ℤ => (h : ZMod p)) := by
      haveI : NeZero p := ⟨hp.ne_zero⟩
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) :=
        fun r _ => hcon r
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_univ, ZMod.card] at h2
      omega
    obtain ⟨r, hr⟩ := hex
    exact ⟨r, fun h hh hcontra => hr (Finset.mem_image.2 ⟨h, hh, hcontra⟩)⟩

/-- The tuple has exactly four elements. -/
