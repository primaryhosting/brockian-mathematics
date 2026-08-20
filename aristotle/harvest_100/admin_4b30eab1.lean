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

open Cardinal

universe u

/-- An ultrafilter `U` on a type `α` is *nonprincipal* if it contains no singleton,
i.e. it is not the principal ultrafilter at any point. -/
def IsNonprincipal {α : Type u} (U : Ultrafilter α) : Prop :=
  ∀ x : α, ({x} : Set α) ∉ U

/-- An ultrafilter `U` on a type `α` is *`c`-complete* if it is closed under
intersections of fewer than `c` many of its members. -/
def IsComplete {α : Type u} (c : Cardinal.{u}) (U : Ultrafilter α) : Prop :=
  ∀ S : Set (Set α), #S < c →
    (∀ s ∈ S, s ∈ U) → ⋂₀ S ∈ U

/-- A cardinal `c` is *measurable* if it is uncountable and there is a nonprincipal
`c`-complete ultrafilter on a type of cardinality `c` (concretely, on `c.ord.ToType`). -/
def IsMeasurableCardinal (c : Cardinal.{u}) : Prop :=
  ℵ₀ < c ∧ ∃ U : Ultrafilter c.ord.ToType, IsNonprincipal U ∧ IsComplete c U

/-- The measurable-cardinal statement: there exists a measurable cardinal, i.e. a cardinal
carrying a nonprincipal `κ`-complete ultrafilter. This is a large-cardinal axiom, strictly
stronger than `Con(ZFC)`, and is *not* proved here. -/
def MeasurableCardinalStatement : Prop :=
  ∃ c : Cardinal.{u}, IsMeasurableCardinal c

/-- Self-equivalence of the measurable-cardinal statement. This merely registers the
statement; it asserts nothing about the existence of measurable cardinals.
(Closed by `Iff.rfl`, i.e. Mathlib's `Iff.refl`.) -/
theorem measurable_statement :
    MeasurableCardinalStatement.{u} ↔ MeasurableCardinalStatement.{u} :=
  Iff.rfl

end LargeCardinal

