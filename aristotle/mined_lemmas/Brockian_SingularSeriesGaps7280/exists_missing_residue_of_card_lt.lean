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

theorem exists_missing_residue_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : H.card < p) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨by omega⟩
  by_contra hcon
  push_neg at hcon
  have huniv : (H.image (fun h : ℤ => (h : ZMod p))) = Finset.univ := by
    refine Finset.eq_univ_of_forall ?_
    intro r
    obtain ⟨h, hh, hhr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨h, hh, hhr⟩
  have hcard : (Finset.univ : Finset (ZMod p)).card ≤ H.card := by
    rw [← huniv]; exact Finset.card_image_le
  rw [Finset.card_univ, ZMod.card p] at hcard
  omega

/-- A tuple all of whose elements are prime to `p` misses the residue class `0` modulo `p`. -/
