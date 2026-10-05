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

theorem exists_politician_of_degree_le_one (hG : UniqueCommonFriend G) [Nonempty V]
    (hd : G.IsRegularOfDegree d) (hd1 : d ≤ 1) : ∃ v : V, IsPolitician G v := by
  have h := card_of_regular hG hd
  have hsq : d * d = d := by interval_cases d <;> norm_num
  rw [hsq] at h
  have hcard : Fintype.card V ≤ 1 := by
    have : 0 < Fintype.card V := Fintype.card_pos
    omega
  exact ⟨Classical.arbitrary V, fun w hw => absurd (Fintype.card_le_one_iff.mp hcard _ w) hw⟩

