/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` before any module docstring, so the header block is repeated
-- below as the module docstring.)

import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open TopologicalSpace

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

/-!
## The countable chain condition

A *cellular family* in a topological space is a family of pairwise disjoint nonempty open
sets.  A space satisfies the *countable chain condition* (ccc) if every cellular family in it
is countable.
-/

/-- A family of pairwise disjoint nonempty open sets. -/

theorem isCCC_iff_countable_of_discrete (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    IsCCC X ↔ Countable X := by
  constructor
  · intro h
    have hcell : IsCellularFamily (Set.range (fun x : X => ({x} : Set X))) := by
      refine ⟨?_, ?_, ?_⟩
      · rintro U ⟨x, rfl⟩; exact isOpen_discrete _
      · rintro U ⟨x, rfl⟩; exact ⟨x, rfl⟩
      · rintro U ⟨x, rfl⟩ V ⟨y, rfl⟩ hUV
        have hxy : x ≠ y := fun hxy => hUV (by rw [hxy])
        simp only [Function.onFun, id_eq, Set.disjoint_singleton]
        exact hxy
    have hc := h _ hcell
    have : Countable (Set.range (fun x : X => ({x} : Set X))) := hc.to_subtype
    have hinj : Function.Injective
        (fun x : X => (⟨({x} : Set X), ⟨x, rfl⟩⟩ : Set.range (fun x : X => ({x} : Set X)))) := by
      intro x y h
      have : ({x} : Set X) = ({y} : Set X) := congrArg Subtype.val h
      simpa using this
    exact hinj.countable
  · intro _
    exact isCCC_of_separableSpace X

/-- Every second countable space satisfies the countable chain condition. -/
