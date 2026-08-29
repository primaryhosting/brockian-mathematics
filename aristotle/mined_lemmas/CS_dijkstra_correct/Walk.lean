/-
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-!
## Setting

A weighted digraph on a finite vertex type `V` is given by a weight function
`w : V → V → ℕ∞`.  Weights live in `ℕ∞ = WithTop ℕ`, so they are automatically
nonnegative, and `w x y = ⊤` encodes "there is no edge from `x` to `y`".
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `RWalk w S s v l`: there is a walk from `s` to `v` of total weight `l`
all of whose vertices, **except possibly the final vertex `v`**, lie in `S`. -/
inductive RWalk (w : V → V → ℕ∞) (S : Finset V) (s : V) : V → ℕ∞ → Prop
  | nil : RWalk w S s s 0
  | cons {x v : V} {l : ℕ∞} : RWalk w S s x l → x ∈ S → RWalk w S s v (l + w x v)

/-- `Walk w s v l`: there is a walk from `s` to `v` of total weight `l`
(no restriction on the intermediate vertices). -/

theorem Walk.cons' {w : V → V → ℕ∞} {s x v : V} {l : ℕ∞} (h : Walk w s x l) :
    Walk w s v (l + w x v) := RWalk.cons h (Finset.mem_univ x)

/-!
## The algorithm

`dijkstraAux w n Q d` performs (at most) `n` rounds of Dijkstra's algorithm.
`Q` is the set of vertices not yet finalized, and `d` is the current tentative
distance array.  Each round selects a vertex `u ∈ Q` of minimal tentative
distance, removes it from `Q`, and relaxes all edges out of `u`.
-/

/-- One round of Dijkstra: relax all edges out of `u`. -/
