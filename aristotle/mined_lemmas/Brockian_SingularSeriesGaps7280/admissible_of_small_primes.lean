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

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` is *admissible* if, for every prime `p`, the reductions of the
elements of `H` modulo `p` do not cover all residue classes mod `p`.  This is exactly the
condition under which the singular series of the tuple `H` is nonzero. -/

theorem admissible_of_small_primes (H : Finset ℤ)
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r) :
    Admissible H := by
  intro p hp
  rcases le_or_gt p H.card with hle | hgt
  · exact h p hp hle
  · haveI : NeZero p := ⟨hp.ne_zero⟩
    have hcard : (H.image (fun x : ℤ => (x : ZMod p))).card < Fintype.card (ZMod p) := by
      have h1 : (H.image (fun x : ℤ => (x : ZMod p))).card ≤ H.card := Finset.card_image_le
      have : Fintype.card (ZMod p) = p := ZMod.card p
      omega
    have : ∃ r : ZMod p, r ∉ H.image (fun x : ℤ => (x : ZMod p)) := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun x : ℤ => (x : ZMod p)) :=
        fun r _ => hcon r
      have := Finset.card_le_card hsub
      simp only [Finset.card_univ] at this
      omega
    obtain ⟨r, hr⟩ := this
    exact ⟨r, fun x hx hcast => hr (Finset.mem_image.2 ⟨x, hx, hcast⟩)⟩

/-- Admissibility is invariant under translation of the tuple. -/
