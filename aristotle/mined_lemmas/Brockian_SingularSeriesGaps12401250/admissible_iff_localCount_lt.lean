import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

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
-/

open scoped BigOperators

namespace Brockian

/-- A finite set `H` of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture) if for every prime `p` the residues
of the elements of `H` modulo `p` do not cover all of `ZMod p`. -/

theorem admissible_iff_localCount_lt (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → localCount H p < p := by
  constructor
  · rintro hH p hp
    obtain ⟨r, hr, hrH⟩ := hH p hp
    have hsub : H.image (· % p) ⊆ (Finset.range p).erase r := by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact Finset.mem_erase.2 ⟨hrH y hy, Finset.mem_range.2 (Nat.mod_lt _ hp.pos)⟩
    have := Finset.card_le_card hsub
    have hcard : ((Finset.range p).erase r).card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.2 hr), Finset.card_range]
    have hp1 : 1 ≤ p := hp.one_lt.le.trans' (by norm_num)
    unfold localCount
    omega
  · intro h p hp
    have hlt := h p hp
    have hsub := image_mod_subset H hp.pos
    have hne : ¬ Finset.range p ⊆ H.image (· % p) := by
      intro hcon
      have := Finset.card_le_card hcon
      rw [Finset.card_range] at this
      exact absurd hlt (by unfold localCount; omega)
    rw [Finset.subset_iff] at hne
    push_neg at hne
    obtain ⟨r, hr, hrmem⟩ := hne
    refine ⟨r, Finset.mem_range.1 hr, ?_⟩
    intro x hx hxr
    exact hrmem (Finset.mem_image.2 ⟨x, hx, hxr⟩)

/-- If a prime `p` exceeds the size of `H`, the residues of `H` cannot cover `ZMod p`. -/
