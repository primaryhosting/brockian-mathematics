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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/

lemma cycBlock_disjoint (k m : ℕ) (hk : 1 ≤ k) :
    Disjoint (cycBlock k m) (cycBlock k (m + k)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [cycBlock, Finset.mem_image, Finset.mem_range] at hx hx'
  obtain ⟨a, ha, hae⟩ := hx
  obtain ⟨b, hb, hbe⟩ := hx'
  have h1 : (m + (k + b)) % (2 * k + 1) = (m + a) % (2 * k + 1) := by
    have := (cycRes_eq_iff k (m + k + b) (m + a)).mp (hbe.trans hae.symm)
    rwa [Nat.add_assoc] at this
  have h2 : (k + b) % (2 * k + 1) = a % (2 * k + 1) := Nat.ModEq.add_left_cancel' m h1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  omega

