import Mathlib

/-!
# Measurable Statement
Category: Frontier Wave 2 (deeper machinery)
Target: LargeCardinal.measurable_statement
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

namespace LargeCardinal

/-- An ultrafilter `F` on a type `α` is *`κ`-complete* if it is closed under intersections
of families of fewer than `κ` many of its members. -/
def IsKappaComplete {α : Type} (κ : Cardinal.{0}) (F : Ultrafilter α) : Prop :=
  ∀ S : Set (Set α), Cardinal.mk S < κ → (∀ t ∈ S, t ∈ F) → ⋂₀ S ∈ F

/-- An ultrafilter is *nonprincipal* if it contains no singleton. -/
def IsNonprincipal {α : Type} (F : Ultrafilter α) : Prop :=
  ∀ x : α, ({x} : Set α) ∉ F

/-- `IsMeasurable κ` says that the cardinal `κ` is a measurable cardinal: `κ` is uncountable
and there exists a nonprincipal `κ`-complete ultrafilter on a type of cardinality `κ`
(concretely, on the canonical well-ordered type `κ.ord.ToType`). -/
def IsMeasurable (κ : Cardinal.{0}) : Prop :=
  Cardinal.aleph0 < κ ∧
    ∃ F : Ultrafilter κ.ord.ToType, IsNonprincipal F ∧ IsKappaComplete κ F

/-- The measurable-cardinal statement: *there exists a measurable cardinal*, i.e. a cardinal
`κ > ℵ₀` carrying a nonprincipal `κ`-complete ultrafilter. -/
def MeasurableCardinalExists : Prop := ∃ κ : Cardinal.{0}, IsMeasurable κ

/-- **Registration of the measurable-cardinal statement.** We record the statement
`MeasurableCardinalExists` and prove only its self-equivalence `P ↔ P`.

Existence of a measurable cardinal is a large-cardinal axiom, strictly stronger than
`Con(ZFC)`, and is *not* proved here (nor is its negation). -/
theorem measurable_statement : MeasurableCardinalExists ↔ MeasurableCardinalExists :=
  Iff.rfl

/-- The same self-equivalence, stated pointwise for each cardinal. -/
theorem measurable_statement_pointwise (κ : Cardinal.{0}) :
    IsMeasurable κ ↔ IsMeasurable κ :=
  Iff.rfl

end LargeCardinal

