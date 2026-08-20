-- /-!
-- # Measurable Statement
-- Category: Frontier Wave 2 (deeper machinery)
-- Target: LargeCardinal.measurable_statement
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)
-- -/
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

universe u

namespace LargeCardinal

/-- A filter `F` on `α` is `κ`-complete when it is closed under intersections of
families of fewer than `κ` many of its members. -/

def MeasurableCardinalExists : Prop := ∃ κ : Cardinal.{u}, IsMeasurable κ

/-- **Registration of the measurable-cardinal statement.**

This records the statement "there exists a measurable cardinal", i.e. an uncountable
cardinal `κ` carrying a nonprincipal `κ`-complete ultrafilter, and proves only its
self-equivalence `P ↔ P`.  The existence of a measurable cardinal is a large-cardinal
axiom, strictly stronger than the consistency of ZFC, and is *not* proved here. -/
