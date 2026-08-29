import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
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

set_option grind.warning false

namespace Math

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A matching `M` of a graph `G` gives, for every matched vertex `v`, a neighbour
`matchedVertex M v` of `v` in `G`, and this assignment is injective on the matched vertices. -/

noncomputable def matchedVertex (M : G.Subgraph) (v : V) : V :=
  if h : ∃ w, M.Adj v w then h.choose else v

