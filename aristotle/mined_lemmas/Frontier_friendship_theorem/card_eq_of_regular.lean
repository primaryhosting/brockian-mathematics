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

import Mathlib

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph satisfies the *friendship condition* when any two distinct vertices have
exactly one common neighbour ("every two people have exactly one common friend"). -/

lemma card_eq_of_regular (hG : Friendship G) {d : ℕ} (hd : ∀ v : V, G.degree v = d) (v : V) :
    d * d + 1 = d + Fintype.card V := by
  have hrow : ∀ u : V, ∑ w : V, (G.adjMatrix ℕ) u w = d := by
    intro u
    simp [adjMatrix_apply, Finset.sum_boole, ← neighborFinset_eq_filter, hd]
  have hsum1 : ∑ w : V, (G.adjMatrix ℕ * G.adjMatrix ℕ) v w = d * d := by
    simp only [adjMatrix_mul_apply]
    rw [Finset.sum_comm]
    simp only [hrow]
    rw [Finset.sum_const, card_neighborFinset_eq_degree, hd, smul_eq_mul]
  have hsum2 : ∑ w : V, (G.adjMatrix ℕ * G.adjMatrix ℕ) v w = d + (Fintype.card V - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    congr 1
    · rw [adjMatrix_sq_apply, Finset.inter_self, card_neighborFinset_eq_degree, hd, Nat.cast_id]
    · rw [Finset.sum_congr rfl (fun w hw => ?_), Finset.sum_const, Finset.card_erase_of_mem
        (Finset.mem_univ v), Finset.card_univ, smul_eq_mul, mul_one]
      rw [adjMatrix_sq_apply, card_common_neighbors_eq_one hG (Ne.symm (Finset.ne_of_mem_erase hw))]
      norm_num
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

/-- A regular friendship graph without a vertex adjacent to all others has degree at least
three. -/
