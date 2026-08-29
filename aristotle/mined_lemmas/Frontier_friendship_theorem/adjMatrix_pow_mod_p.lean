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

theorem adjMatrix_pow_mod_p (hG : UniqueCommonFriend G) {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : ∀ k : ℕ, 2 ≤ k →
      G.adjMatrix (ZMod p) ^ k = Matrix.of (fun _ _ => (1 : ZMod p)) := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hn2 : n = 1 := by omega
      subst hn2
      rw [adjMatrix_sq_of_regular hG (ZMod p) hd]
      ext v w
      rcases eq_or_ne v w with rfl | hvw
      · simp [dmod]
      · simp [hvw]
    · rw [pow_succ', ih hn, adjMatrix_mul_allOnes (ZMod p) hd, dmod]

