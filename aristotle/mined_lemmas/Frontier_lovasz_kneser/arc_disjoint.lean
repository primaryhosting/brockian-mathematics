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

/-! ## The Kneser graph -/

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/

lemma arc_disjoint (i : ℕ) : Disjoint (arc k i) (arc k (i + k)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_arc] at hx hx'
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨s, hs, hxs⟩ := hx'
  have h1 : (i + t) % (2 * k + 1) = (i + (k + s)) % (2 * k + 1) := by
    rw [← hxt, hxs]; ring_nf
  have h2 : t % (2 * k + 1) = (k + s) % (2 * k + 1) := Nat.ModEq.add_left_cancel' i h1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  omega

