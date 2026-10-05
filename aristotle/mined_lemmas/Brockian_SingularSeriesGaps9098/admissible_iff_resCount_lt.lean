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

theorem admissible_iff_resCount_lt (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → resCount H p < p := by
  constructor
  · intro hH p hp
    obtain ⟨r, hrp, hr⟩ := hH p hp
    have hsub : H.image (· % p) ⊆ (Finset.range p).erase r := by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨h, hh, rfl⟩ := hx
      exact Finset.mem_erase.2 ⟨hr h hh, Finset.mem_range.2 (Nat.mod_lt _ hp.pos)⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 hrp), Finset.card_range] at this
    have hp1 : 1 ≤ p := hp.one_lt.le.trans_eq' (by norm_num)
    exact lt_of_le_of_lt this (by omega)
  · intro hH p hp
    have hlt : (H.image (· % p)).card < p := hH p hp
    have hsub : H.image (· % p) ⊆ Finset.range p := by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨h, _, rfl⟩ := hx
      exact Finset.mem_range.2 (Nat.mod_lt _ hp.pos)
    have hne : H.image (· % p) ≠ Finset.range p := by
      intro h
      rw [h, Finset.card_range] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨r, hr, hrmem⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
    refine ⟨r, Finset.mem_range.1 hr, ?_⟩
    intro h hh hmod
    exact hrmem (Finset.mem_image.2 ⟨h, hh, hmod⟩)

/-- A prime larger than the cardinality of `H` can never be covered by `H`. -/
