import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The set of residue classes modulo `p` occupied by the tuple `H`. -/

lemma admissible_iff (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → localCount H p < p := by
  constructor
  · intro hH p hp
    obtain ⟨r, hrp, hr⟩ := hH p hp
    have hsub : residues H p ⊆ (Finset.range p).erase r := by
      intro s hs
      have hs' := residues_subset_range H hp.pos hs
      refine Finset.mem_erase.mpr ⟨?_, hs'⟩
      simp only [residues, Finset.mem_image] at hs
      obtain ⟨h, hh, rfl⟩ := hs
      exact hr h hh
    have hcard : ((Finset.range p).erase r).card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hrp), Finset.card_range]
    have hle : localCount H p ≤ p - 1 := by
      simpa [localCount, hcard] using Finset.card_le_card hsub
    have hp1 : 2 ≤ p := hp.two_le
    omega
  · intro hH p hp
    have hlt : (residues H p).card < (Finset.range p).card := by
      simpa [localCount, Finset.card_range] using hH p hp
    obtain ⟨r, hr, hr'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨r, Finset.mem_range.mp hr, ?_⟩
    intro h hh hcon
    exact hr' (by simp only [residues, Finset.mem_image]; exact ⟨h, hh, hcon⟩)

