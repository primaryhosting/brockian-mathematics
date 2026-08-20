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

namespace Chem

open Polynomial Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₇` (the Hückel matrix of cycloheptatrienyl,
with `α = 0`, `β = 1`), as a real `7 × 7` matrix. -/

lemma sum_ee (c : Fin 7) : (∑ k : Fin 7, ee (k * c)) = if c = 0 then 7 else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [ee_zero]
  · rw [if_neg hc]
    have key : ee c * (∑ k : Fin 7, ee (k * c)) = ∑ k : Fin 7, ee (k * c) := by
      rw [Finset.mul_sum]
      have hstep : ∀ k : Fin 7, ee c * ee (k * c) = ee ((k + 1) * c) := by
        intro k
        rw [fin7_succ_mul k c, ee_add]
      simp_rw [hstep]
      exact Fintype.sum_equiv (Equiv.addRight (1 : Fin 7)) _ _ (fun _ => rfl)
    have h0 : (ee c - 1) * (∑ k : Fin 7, ee (k * c)) = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) (ee_ne_one hc)
    · exact h

/-- The eigenvalues of the adjacency matrix, in complex form. -/
