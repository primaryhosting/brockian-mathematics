/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
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
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- A finite set of nonnegative integers is *admissible* (in the Hardy–Littlewood /
Hensley–Richards sense) if for every prime `p` it fails to cover all residue classes
modulo `p`.  Equivalently, the singular series attached to the tuple is nonzero. -/

theorem exists_uncovered_residue (H : Finset ℕ) (p : ℕ) (hcard : H.card < p) :
    ∃ r < p, ∀ h ∈ H, h % p ≠ r := by
  have hlt : (H.image (fun x => x % p)).card < (Finset.range p).card := by
    calc (H.image (fun x => x % p)).card ≤ H.card := Finset.card_image_le
      _ < p := hcard
      _ = (Finset.range p).card := (Finset.card_range p).symm
  obtain ⟨r, hr, hrnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨r, Finset.mem_range.mp hr, ?_⟩
  intro h hh hcon
  exact hrnot (Finset.mem_image.mpr ⟨h, hh, hcon⟩)

/-- The primes below `141`. -/
