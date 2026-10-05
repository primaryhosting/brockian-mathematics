import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Brockian

/-- The gap window: the integers of the range `[1450, 1460]`. -/

lemma exists_missing_iff (H : Finset ℤ) (p : ℕ) [NeZero p] :
    (∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r) ↔ nu H p < p := by
  constructor
  · rintro ⟨r, hr⟩
    have hsub : (H.image (Int.cast : ℤ → ZMod p)) ⊆ Finset.univ.erase r := by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨h, hh, rfl⟩ := hx
      exact Finset.mem_erase.mpr ⟨hr h hh, Finset.mem_univ _⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, ZMod.card] at hcard
    have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    simp only [nu]
    omega
  · intro h
    by_contra hcon
    push_neg at hcon
    have himg : (H.image (Int.cast : ℤ → ZMod p)) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro r
      obtain ⟨x, hx, hxr⟩ := hcon r
      simp only [Finset.mem_image]
      exact ⟨x, hx, hxr⟩
    simp only [nu, himg, Finset.card_univ, ZMod.card] at h
    exact lt_irrefl _ h

