import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
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

namespace CS

/-! ## Walks

A walk starting at a vertex `src` is described by the list `l` of vertices it visits
after `src`, in order.  Since we work with a complete weighted graph (a non-edge can be
modelled by a suitably large weight), every list of vertices describes a walk. -/

section Walks

variable {V : Type*}

/-- The final vertex of the walk that starts at `src` and then visits `l` in order. -/

noncomputable def dijkstraInit (w : V → V → ℝ) (src : V) : Finset V × (V → ℝ) :=
  ({src}, fun v => if v = src then 0 else w src v)

/-- Dijkstra's algorithm: iterate the settle-and-relax step `|V|` times. -/
