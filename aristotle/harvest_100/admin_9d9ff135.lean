/-
# Measurable Statement
Category: Frontier Wave 2 (deeper machinery)
Target: LargeCardinal.measurable_statement
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

universe u v

namespace LargeCardinal

/-- An ultrafilter `U` on a type `α` is *`κ`-complete* when it is closed under
intersections of families of fewer than `κ` many of its members. -/
def IsKappaComplete {α : Type u} (U : Ultrafilter α) (kappa : Cardinal.{v}) : Prop :=
  ∀ S : Set (Set α), Cardinal.lift.{v} (Cardinal.mk S) < Cardinal.lift.{u} kappa →
    (∀ s ∈ S, s ∈ U) → ⋂₀ S ∈ U

/-- An ultrafilter is *nonprincipal* when no singleton belongs to it. -/
def IsNonprincipal {α : Type u} (U : Ultrafilter α) : Prop :=
  ∀ a : α, ({a} : Set α) ∉ U

/-- A cardinal `κ` is *measurable* when it is uncountable and there exists a
nonprincipal `κ`-complete ultrafilter on (a set of order type) `κ`. -/
def IsMeasurableCardinal (kappa : Cardinal.{u}) : Prop :=
  Cardinal.aleph0 < kappa ∧
    ∃ U : Ultrafilter kappa.ord.ToType,
      IsNonprincipal U ∧ IsKappaComplete U kappa

/-- The large-cardinal statement: there exists a measurable cardinal.
This is *not* provable in ZFC; here it is only registered as a `Prop`. -/
def ExistsMeasurableCardinal : Prop := ∃ kappa : Cardinal.{u}, IsMeasurableCardinal kappa

/-- The registered measurable-cardinal statement, proved only in the trivial
self-equivalent form `P ↔ P`. No existence claim is made. -/
theorem measurable_statement :
    ExistsMeasurableCardinal.{u} ↔ ExistsMeasurableCardinal.{u} :=
  Iff.rfl

end LargeCardinal

