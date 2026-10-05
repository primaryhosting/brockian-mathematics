/-
# Measurable Statement
Category: Frontier Wave 2 (deeper machinery)
Target: LargeCardinal.measurable_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

universe u

/-- A filter `f` on `α` is `kappa`-complete when the intersection of any family of
fewer than `kappa` members of `f` again belongs to `f`. -/
def IsKappaComplete (kappa : Cardinal.{u}) {α : Type u} (f : Filter α) : Prop :=
  ∀ s : Set (Set α), Cardinal.mk s < kappa → (∀ t ∈ s, t ∈ f) → ⋂₀ s ∈ f

/-- An ultrafilter is nonprincipal when it is not the principal (pure) ultrafilter at
any point. -/
def IsNonprincipal {α : Type u} (U : Ultrafilter α) : Prop :=
  ¬ ∃ a : α, (U : Filter α) = (Pure.pure a : Filter α)

/-- `kappa` is a *measurable cardinal*: it is uncountable and carries a nonprincipal
`kappa`-complete ultrafilter on a type of cardinality `kappa`. -/
def IsMeasurableCardinal (kappa : Cardinal.{u}) : Prop :=
  Cardinal.aleph0 < kappa ∧
    ∃ (α : Type u) (_ : Cardinal.mk α = kappa) (U : Ultrafilter α),
      IsNonprincipal U ∧ IsKappaComplete kappa (U : Filter α)

/-- The measurable-cardinal statement: there exists a measurable cardinal.

This is a large-cardinal axiom, strictly stronger than the consistency of ZFC, and is
neither provable nor refutable here. We only register the statement. -/
def MeasurableStatementProp : Prop := ∃ kappa : Cardinal.{u}, IsMeasurableCardinal kappa

/-- The self-equivalence of the measurable-cardinal statement. This records the
statement formally; it makes no claim about the existence of measurable cardinals. -/
theorem measurable_statement :
    MeasurableStatementProp.{u} ↔ MeasurableStatementProp.{u} :=
  Iff.rfl

end LargeCardinal

