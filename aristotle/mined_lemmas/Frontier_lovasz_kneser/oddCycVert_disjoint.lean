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

lemma oddCycVert_disjoint (k j : ℕ) : Disjoint (oddCycVert k j) (oddCycVert k (j + 1)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [oddCycVert, Finset.mem_image, Finset.mem_range] at hx hx'
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hba⟩ := hx'
  rw [oddElt_eq_iff] at hba
  have h : (k + b) ≡ a [MOD 2 * k + 1] := by
    refine Nat.ModEq.add_left_cancel' (j * k) ?_
    unfold Nat.ModEq
    rw [← hba]
    ring_nf
  unfold Nat.ModEq at h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  omega

