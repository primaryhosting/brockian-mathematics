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

theorem RWalk.toWalk {w : V → V → ℕ∞} {S : Finset V} {s v : V} {l : ℕ∞}
    (h : RWalk w S s v l) : Walk w s v l :=
  h.mono (Finset.subset_univ S)

omit [DecidableEq V] in
