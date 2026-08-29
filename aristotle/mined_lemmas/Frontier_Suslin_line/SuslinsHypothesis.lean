/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` before any module docstring, so the header block is repeated
-- below as the module docstring.)

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

open TopologicalSpace

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

/-!
## The countable chain condition

A *cellular family* in a topological space is a family of pairwise disjoint nonempty open
sets.  A space satisfies the *countable chain condition* (ccc) if every cellular family in it
is countable.
-/

/-- A family of pairwise disjoint nonempty open sets. -/

def SuslinsHypothesis : Prop :=
  ∀ (X : Type) [LinearOrder X] [TopologicalSpace X] [OrderTopology X],
    DenselyOrdered X → NoMinOrder X → NoMaxOrder X → IsCCC X → SeparableSpace X

/-- Suslin's problem, precisely stated: a Suslin line exists if and only if Suslin's
Hypothesis fails. -/
