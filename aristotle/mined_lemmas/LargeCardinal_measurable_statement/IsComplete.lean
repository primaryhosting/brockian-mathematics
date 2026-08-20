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

def IsComplete {α : Type u} (c : Cardinal.{u}) (U : Ultrafilter α) : Prop :=
  ∀ S : Set (Set α), #S < c →
    (∀ s ∈ S, s ∈ U) → ⋂₀ S ∈ U

/-- A cardinal `c` is *measurable* if it is uncountable and there is a nonprincipal
`c`-complete ultrafilter on a type of cardinality `c` (concretely, on `c.ord.ToType`). -/
