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

theorem exists_missed_class_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : H.card < p) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨by omega⟩
  have hcard : (H.image (fun h : ℤ => (h : ZMod p))).card < p :=
    lt_of_le_of_lt Finset.card_image_le hp
  have hex : ∃ r : ZMod p, r ∉ H.image (fun h : ℤ => (h : ZMod p)) := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) :=
      fun r _ => hcon r
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at h2
    omega
  obtain ⟨r, hr⟩ := hex
  exact ⟨r, fun h hh hcontra => hr (Finset.mem_image.2 ⟨h, hh, hcontra⟩)⟩

/-- `resCount H p = ν_p(H)` is the number of residue classes modulo `p` occupied by `H`; it is
the local factor entering the singular series `𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}`. -/
