/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* if for every prime `p` the elements of `H`
do not cover all residue classes modulo `p`.  This is exactly the condition under which the
Hardy–Littlewood singular series `𝔖(H)` of the tuple `H` is nonzero. -/

theorem admissible_iff_resCount_lt (H : Finset ℤ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → resCount H p < p := by
  constructor
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨r, hr⟩ := hH p hp
    have hsub : (H.image (fun h : ℤ => (h : ZMod p))) ⊆ (Finset.univ : Finset (ZMod p)).erase r := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_erase.mpr ⟨hr h hh, Finset.mem_univ _⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, ZMod.card p] at hcard
    have hp0 : 0 < p := hp.pos
    exact lt_of_le_of_lt hcard (by omega)
  · intro hH p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    by_contra hcon
    push_neg at hcon
    have huniv : (H.image (fun h : ℤ => (h : ZMod p))) = Finset.univ := by
      refine Finset.eq_univ_of_forall ?_
      intro r
      obtain ⟨h, hh, hhr⟩ := hcon r
      exact Finset.mem_image.mpr ⟨h, hh, hhr⟩
    have := hH p hp
    rw [resCount, huniv, Finset.card_univ, ZMod.card p] at this
    omega

/-- The local factor of the Hardy–Littlewood singular series of a `k`-tuple `H` at the prime `p`:
`(1 - ν_p(H)/p) / (1 - 1/p)^k`. -/
