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

set_option maxRecDepth 10000
set_option synthInstance.maxSize 400
set_option synthInstance.maxHeartbeats 1000000

namespace Math

open Finset SimpleGraph

/-- `HasRamseyProp34 n` holds when every simple graph on `n` vertices contains either a
clique of size `3` or an independent set of size `4`; equivalently, every red/blue colouring
of the edges of `K n` contains a red triangle or a blue `K 4`. -/

def HasRamseyProp34 (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), s.card = 3 ∧ G.IsClique (↑s : Set (Fin n))) ∨
    (∃ t : Finset (Fin n), t.card = 4 ∧ G.IsIndepSet (↑t : Set (Fin n)))

/-! ### Building cliques and independent sets from explicit vertices -/

