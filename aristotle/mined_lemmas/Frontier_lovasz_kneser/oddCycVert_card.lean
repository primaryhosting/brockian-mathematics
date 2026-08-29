import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
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

namespace Frontier

/-- Vertices of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an `n`-element set. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-subsets of `Fin n`, and two
distinct vertices are adjacent when the corresponding sets are disjoint. -/

lemma oddCycVert_card (k j : ℕ) : (oddCycVert k j).card = k := by
  rw [oddCycVert, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_range] at ha hb
  rw [oddElt_eq_iff] at hab
  have h : a ≡ b [MOD 2 * k + 1] := Nat.ModEq.add_left_cancel' (j * k) hab
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h

