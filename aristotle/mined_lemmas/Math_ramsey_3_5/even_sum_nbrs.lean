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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Math

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s`, or an independent set of size `t` (a clique of size `t` in the complement).
Equivalently, every 2-colouring of the edges of `K n` has a red `K s` or a blue `K t`. -/

lemma even_sum_nbrs (A : Finset V) : Even (∑ v ∈ A, (nbrs G A v).card) := by
  have key : ∀ v ∈ A, (nbrs G A v).card = ∑ u ∈ A, (if G.Adj v u then 1 else 0) := by
    intro v _
    rw [nbrs_eq_filter, Finset.card_filter]
  rw [Finset.sum_congr rfl key]
  refine even_sum_symm (fun x y => if G.Adj x y then 1 else 0) (fun x y => ?_)
    (fun x => ?_) A
  · simp [SimpleGraph.adj_comm]
  · simp

end Parity

/-! ## The upper bound `R(3,5) ≤ 14` -/

section Upper

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

