/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

open Classical in
/-- `chainHeight x` is the largest cardinality of a chain all of whose elements are `≤ x`. -/

lemma card_chain_le_card_cover {F : Finset (Finset α)}
    (hanti : ∀ A ∈ F, IsAntichain (· ≤ ·) (A : Set α)) (hcov : ∀ x : α, ∃ A ∈ F, x ∈ A)
    {s : Finset α} (hs : IsChain (· ≤ ·) (s : Set α)) : s.card ≤ F.card := by
  classical
  choose pick hpickF hpickmem using hcov
  refine Finset.card_le_card_of_injOn pick (fun x _ => hpickF x) ?_
  intro x hx y hy hxy
  by_contra hne
  have hxA : x ∈ pick x := hpickmem x
  have hyA : y ∈ pick x := hxy ▸ hpickmem y
  have hanti' := hanti (pick x) (hpickF x)
  rcases hs (by simpa using hx) (by simpa using hy) hne with h | h
  · exact hanti' hxA hyA hne h
  · exact hanti' hyA hxA (Ne.symm hne) h


open Classical in
/-- The maximum size of a chain in a finite partial order. -/
