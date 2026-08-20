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

/-- A finite set of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when, for every prime `p`, it misses at least one
residue class modulo `p`.  Equivalently, the singular series attached to the tuple
is nonzero. -/

theorem admissibleSet_of_small_primes {H : Finset ℤ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r) :
    AdmissibleSet H := by
  intro p hp
  by_cases hle : p ≤ H.card
  · exact h p hp hle
  · push_neg at hle
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hcard : (H.image (fun x : ℤ => (x : ZMod p))).card < Finset.univ.card (α := ZMod p) := by
      have h1 : (H.image (fun x : ℤ => (x : ZMod p))).card ≤ H.card := Finset.card_image_le
      have h2 : Finset.univ.card (α := ZMod p) = p := by
        simp [ZMod.card p]
      omega
    have : ∃ r : ZMod p, r ∉ H.image (fun x : ℤ => (x : ZMod p)) := by
      by_contra hcon
      push_neg at hcon
      have : Finset.univ ⊆ H.image (fun x : ℤ => (x : ZMod p)) := fun r _ => hcon r
      have := Finset.card_le_card this
      omega
    obtain ⟨r, hr⟩ := this
    refine ⟨r, ?_⟩
    intro x hx hcontra
    exact hr (Finset.mem_image.mpr ⟨x, hx, hcontra⟩)

/-- The `9`-tuple of shifts studied here: an admissible pattern of `9` integers of
diameter `30`. -/
