/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
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

namespace Math

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
/-- Exhaustive check over the `2 ^ 15` two-colorings of the edges of `K₆`
(the edge between `i < j` is coloured `eij`): some triple `i < j < k` is
monochromatic. -/

def cycleGraph5 : SimpleGraph (Fin 5) where
  Adj i j := pentagon i j = true
  symm := by
    intro a b h
    simpa [pentagon, Bool.or_comm] using h
  loopless := ⟨by decide⟩

instance : DecidableRel cycleGraph5.Adj := fun i j => by
  unfold cycleGraph5; infer_instance

/--
**R(3,3) = 6, graph-theoretic form.**

For every simple graph `G` on six vertices, either `G` or its complement
contains a triangle; and there is a graph on five vertices (the 5-cycle) such
that neither it nor its complement contains a triangle.
-/
