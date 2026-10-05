/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The number of residue classes modulo `p` occupied by a finite set `H` of natural numbers.
This is the quantity `ν_H(p)` appearing in the Euler factors of the Hardy–Littlewood
singular series of the tuple `H`. -/

theorem exists_missed_residue_of_card_lt (H : Finset ℕ) {p : ℕ} (hp : 0 < p)
    (hcard : H.card < p) : ∃ r < p, ∀ h ∈ H, h % p ≠ r := by
  have hsub : H.image (· % p) ⊆ Finset.range p := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨h, _, rfl⟩ := hx
    exact Finset.mem_range.2 (Nat.mod_lt _ hp)
  have hlt : (H.image (· % p)).card < (Finset.range p).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt (Finset.card_image_le) hcard
  have hne : H.image (· % p) ≠ Finset.range p := fun h => by
    rw [h] at hlt; exact lt_irrefl _ hlt
  obtain ⟨r, hr, hrmem⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
  refine ⟨r, Finset.mem_range.1 hr, ?_⟩
  intro h hh hmod
  exact hrmem (Finset.mem_image.2 ⟨h, hh, hmod⟩)

/-- Admissibility is a *finite* condition: it suffices to check the primes `p ≤ |H|`. -/
