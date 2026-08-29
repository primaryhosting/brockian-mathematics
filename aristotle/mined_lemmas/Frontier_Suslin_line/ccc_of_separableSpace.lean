import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
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

namespace Frontier

/-! ## The countable chain condition -/

/-- A topological space satisfies the **countable chain condition** (ccc) if every family of
pairwise disjoint nonempty open sets is countable. -/

theorem ccc_of_separableSpace (α : Type) [TopologicalSpace α] [TopologicalSpace.SeparableSpace α] :
    CCC α := fun _ hopen hne hdisj =>
  Set.PairwiseDisjoint.countable_of_isOpen (s := id) hdisj hopen hne

/-- The countable chain condition is a topological invariant. -/
