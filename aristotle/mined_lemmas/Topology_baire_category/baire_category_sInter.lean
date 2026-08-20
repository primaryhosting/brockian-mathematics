import Mathlib

/-!
# Baire Category
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.baire_category
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

namespace Topology

/-- **The Baire category theorem.** In a complete metric space `X`, the intersection of a
countable family `f : ι → Set X` of dense open sets is dense. -/

theorem baire_category_sInter {X : Type*} [MetricSpace X] [CompleteSpace X]
    (S : Set (Set X)) (hS : S.Countable)
    (ho : ∀ s ∈ S, IsOpen s) (hd : ∀ s ∈ S, Dense s) :
    Dense (⋂₀ S) := by
  rw [Set.sInter_eq_biInter, Set.biInter_eq_iInter]
  haveI : Countable S := hS.to_subtype
  exact baire_category (fun s : S => (s : Set X)) (fun s => ho s s.2) (fun s => hd s s.2)

/-- In a nonempty complete metric space, a countable intersection of dense open sets is
nonempty. -/
