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
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {d : ℕ}

/-- The friendship hypothesis: any two distinct vertices have exactly one common neighbour. -/

theorem exists_isRegularOfDegree_of_not_politician [Nonempty V] (hG : UniqueCommonFriend G)
    (hnp : ¬ ∃ v : V, IsPolitician G v) : ∃ d : ℕ, G.IsRegularOfDegree d := by
  have hnp' : ∀ v : V, ∃ w : V, v ≠ w ∧ ¬ G.Adj v w := by
    simpa [IsPolitician, not_forall] using hnp
  refine ⟨G.degree (Classical.arbitrary V), fun x => ?_⟩
  set v := Classical.arbitrary V with hv
  by_cases hvx : G.Adj v x
  swap
  · exact (degree_eq_of_not_adj hG hvx).symm
  obtain ⟨w, hvw', hvw⟩ := hnp' v
  obtain ⟨y, hxy', hxy⟩ := hnp' x
  by_cases hxw : G.Adj x w
  swap
  · rw [degree_eq_of_not_adj hG hvw]
    exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v y
  swap
  · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  refine degree_eq_of_not_adj hG (fun hyw => hxy' ?_)
  obtain ⟨a, -, huniq⟩ := hG v w hvw'
  rw [huniq x ⟨hvx, hxw.symm⟩, huniq y ⟨hvy, hyw.symm⟩]

/-- For a `d`-regular friendship graph, `A ^ 2` is determined completely. -/
