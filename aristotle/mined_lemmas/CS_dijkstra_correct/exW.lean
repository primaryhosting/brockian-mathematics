import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Statement: Dijkstra's algorithm computes shortest-path distances on nonnegative-weight graphs.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Walks and shortest-path distances

A weighted digraph on the finite vertex type `V` is given by a weight function
`w : V → V → ℕ∞`, where `w u v = ⊤` encodes the absence of an edge from `u` to `v`.
All weights are nonnegative by construction. -/

/-- `walkCost w u l` is the total weight of the walk that starts at `u` and then visits
the vertices of `l` in order. -/

private def exW : Fin 3 → Fin 3 → ℕ∞ := fun a b =>
  if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 2 then 1 else if a = 0 ∧ b = 2 then 5 else ⊤

example : sdist exW 0 2 ≤ 2 ∧ exW 0 2 = 5 := by
  refine ⟨?_, by decide⟩
  have h : sdist exW 0 2 ≤ walkCost exW 0 [1, 2] := sdist_le_walkCost exW 0 2 rfl
  simpa [walkCost, exW] using h

#print axioms CS.dijkstra_correct

end CS

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

