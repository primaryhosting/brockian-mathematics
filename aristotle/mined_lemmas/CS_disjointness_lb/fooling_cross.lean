import Mathlib

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

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u v

/-- A deterministic two-party communication protocol: a binary tree whose internal nodes
are labelled either by a bit that Alice sends (a function of her input `x : X`) or by a bit
that Bob sends (a function of his input `y : Y`), and whose leaves carry the output bit. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The communication cost of a protocol: the depth of the tree, i.e. the worst-case number
of bits exchanged. -/

theorem fooling_cross {n : ℕ} {S T : Finset (Fin n)} (h : S ≠ T) :
    ¬ Disjoint S Tᶜ ∨ ¬ Disjoint T Sᶜ := by
  classical
  rw [Ne, Finset.ext_iff] at h
  obtain ⟨a, ha⟩ := not_forall.mp h
  by_cases haS : a ∈ S
  · have haT : a ∉ T := fun hh => ha ⟨fun _ => hh, fun _ => haS⟩
    exact Or.inl (Finset.not_disjoint_iff.mpr ⟨a, haS, by simpa using haT⟩)
  · have haT : a ∈ T := by
      by_contra hh
      exact ha ⟨fun z => absurd z haS, fun z => absurd z hh⟩
    exact Or.inr (Finset.not_disjoint_iff.mpr ⟨a, haT, by simpa using haS⟩)

/-- For a single deterministic protocol that never accepts an intersecting pair, the number of
sets `S` for which the pair `(S, Sᶜ)` is accepted is at most `2 ^ cost`. -/
