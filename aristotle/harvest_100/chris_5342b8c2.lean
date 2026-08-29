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

universe u

namespace LargeCardinal

/-- A filter `F` on a type `α` is `κ`-complete when it is closed under intersections of
families of sets indexed by a type of cardinality strictly less than `κ`. -/
def IsKappaComplete {α : Type u} (kappa : Cardinal.{u}) (F : Filter α) : Prop :=
  ∀ (ι : Type u) (s : ι → Set α), Cardinal.mk ι < kappa → (∀ i : ι, s i ∈ F) →
    (⋂ i : ι, s i) ∈ F

/-- An ultrafilter is *nonprincipal* if it is not the principal ultrafilter at any point. -/
def IsNonprincipal {α : Type u} (U : Ultrafilter α) : Prop :=
  ∀ a : α, U ≠ Ultrafilter.pure a

/-- `IsMeasurableCardinal kappa` says that `kappa` is a measurable cardinal: it is
uncountable and, on some type of cardinality `kappa`, there exists a nonprincipal
`kappa`-complete ultrafilter. -/
def IsMeasurableCardinal (kappa : Cardinal.{u}) : Prop :=
  Cardinal.aleph0 < kappa ∧
    ∃ (α : Type u) (_ : Cardinal.mk α = kappa) (U : Ultrafilter α),
      IsNonprincipal U ∧ IsKappaComplete kappa (U : Filter α)

/-- The measurable-cardinal statement: there exists a measurable cardinal, i.e. an
uncountable cardinal `kappa` carrying a nonprincipal `kappa`-complete ultrafilter. -/
def MeasurableCardinalExists : Prop := ∃ kappa : Cardinal.{u}, IsMeasurableCardinal kappa

/-- Registration of the measurable-cardinal statement: we prove only its self-equivalence.
The existence of a measurable cardinal is a large-cardinal axiom, strictly stronger than
the consistency of ZFC, and is *not* asserted or proved here. -/
theorem measurable_statement :
    MeasurableCardinalExists.{u} ↔ MeasurableCardinalExists.{u} := Iff.rfl

end LargeCardinal

