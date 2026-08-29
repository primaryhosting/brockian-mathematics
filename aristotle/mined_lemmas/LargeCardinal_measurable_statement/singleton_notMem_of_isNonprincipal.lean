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

theorem singleton_notMem_of_isNonprincipal {α : Type u} (F : Ultrafilter α)
    (h : IsNonprincipal (F : Filter α)) (x : α) : ({x} : Set α) ∉ F :=
  fun hx => F.compl_not_mem hx (h x)

/-- The registered target: the self-equivalence of the measurable-cardinal statement.
No existence claim is made. -/
