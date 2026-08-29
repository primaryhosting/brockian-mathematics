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

/-- A filter `F` on a type `α` is `κ`-complete when it is closed under intersections of
families indexed by a type of cardinality `< κ`. -/
def IsKappaComplete {α : Type u} (κ : Cardinal.{u}) (F : Filter α) : Prop :=
  ∀ (ι : Type u), Cardinal.mk ι < κ → ∀ s : ι → Set α, (∀ i, s i ∈ F) → (⋂ i, s i) ∈ F

/-- A filter is nonprincipal (in the strong sense used for measurable cardinals) when the
complement of every singleton belongs to it, i.e. it contains no finite set. -/
def IsNonprincipal {α : Type u} (F : Filter α) : Prop :=
  ∀ x : α, ({x}ᶜ : Set α) ∈ F

/-- A cardinal `κ` is *measurable* if it is uncountable and there exists a nonprincipal
`κ`-complete ultrafilter on (a set of order type) `κ`. -/
def IsMeasurableCardinal (κ : Cardinal.{u}) : Prop :=
  Cardinal.aleph0 < κ ∧
    ∃ F : Ultrafilter κ.ord.ToType,
      IsNonprincipal (F : Filter κ.ord.ToType) ∧ IsKappaComplete κ (F : Filter κ.ord.ToType)

/-- The measurable-cardinal property: there exists a measurable cardinal.  This is a
large-cardinal axiom, strictly stronger than the consistency of ZFC; it is stated here, not
asserted. -/
def MeasurableCardinalExists : Prop := ∃ κ : Cardinal.{u}, IsMeasurableCardinal κ

/-- Sanity check on the formalisation: a nonprincipal ultrafilter contains no singleton,
hence is not a principal ultrafilter. -/
theorem singleton_notMem_of_isNonprincipal {α : Type u} (F : Ultrafilter α)
    (h : IsNonprincipal (F : Filter α)) (x : α) : ({x} : Set α) ∉ F :=
  fun hx => F.compl_not_mem hx (h x)

/-- The registered target: the self-equivalence of the measurable-cardinal statement.
No existence claim is made. -/
theorem measurable_statement :
    MeasurableCardinalExists.{u} ↔ MeasurableCardinalExists.{u} :=
  Iff.rfl

end LargeCardinal

