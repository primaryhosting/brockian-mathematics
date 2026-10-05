/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

/-- A finite set of integers `H` (a "gap pattern") is *admissible* when, for every prime `p`,
the elements of `H` do not cover all residue classes modulo `p`.  This is exactly the condition
under which the associated singular series is nonzero, i.e. the Hardy–Littlewood prime tuple
conjecture predicts infinitely many translates of `H` consisting entirely of primes. -/

theorem exists_missing_residue (H : Finset ℤ) (p : ℕ) [NeZero p] (hcard : H.card < p) :
    ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun x : ℤ => (x : ZMod p)) := by
    intro r _
    obtain ⟨x, hx, hxr⟩ := hcon r
    exact Finset.mem_image.mpr ⟨x, hx, hxr⟩
  have h1 : Fintype.card (ZMod p) ≤ (H.image (fun x : ℤ => (x : ZMod p))).card := by
    simpa [Finset.card_univ] using Finset.card_le_card hsub
  have h2 : (H.image (fun x : ℤ => (x : ZMod p))).card ≤ H.card := Finset.card_image_le
  rw [ZMod.card p] at h1
  omega

/-- Admissibility only needs to be checked at primes `p ≤ H.card`. -/
