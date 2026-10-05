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

set_option grind.warning false

namespace Math

variable {α : Type*} [PartialOrder α]

/-- The finset of all chains (as finsets) contained in a given finset `t`. -/

lemma longestChain_le_card_of_cover {F : Finset (Finset α)} (hF : IsAntichainCover F) :
    longestChain α ≤ F.card := by
  classical
  obtain ⟨s, -, hchain, hcard⟩ := exists_chain_card_eq (Finset.univ : Finset α)
  choose g hgF hxg using hF.2
  rw [longestChain, ← hcard]
  refine Finset.card_le_card_of_injOn g (fun x _ => hgF x) ?_
  intro x hx y hy hxy
  by_contra hne
  have := hchain (by simpa using hx) (by simpa using hy) hne
  have hanti := hF.1 (g x) (hgF x)
  rcases this with h | h
  · exact hanti (hxg x) (by rw [hxy]; exact hxg y) hne h
  · exact hanti (by rw [hxy]; exact hxg y) (hxg x) (Ne.symm hne) h

/-- **Dilworth-type theorem (Mirsky's theorem).**  In a finite poset, the minimum number of
antichains needed to cover the poset equals the cardinality of a longest chain. -/
