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

open Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₄`, viewed with vertex set `ZMod 14`
(which is definitionally `Fin 14`). -/

lemma C14_mul_P : C14 * P = P * Matrix.diagonal lam := by
  ext i k
  have hne : (i - 1 : ZMod 14) ≠ i + 1 := by
    intro h
    have : (2 : ZMod 14) = 0 := by linear_combination -h
    revert this
    decide
  have hL : (C14 * P) i k = ch ((i - 1) * k) + ch ((i + 1) * k) := by
    rw [Matrix.mul_apply]
    have : (∑ j : ZMod 14, C14 i j * P j k)
        = (C14.mulVec (fun j => P j k)) i := rfl
    rw [this, C14, SimpleGraph.adjMatrix_mulVec_apply]
    rw [show (SimpleGraph.cycleGraph 14).neighborFinset i = {i - 1, i + 1} from
      SimpleGraph.cycleGraph_neighborFinset (n := 12)]
    rw [Finset.sum_pair hne]
    rfl
  have hR : (P * Matrix.diagonal lam) i k = ch (i * k) * lam k := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single k]
    · simp [Matrix.diagonal_apply_eq, P]
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ hb]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [hL, hR, lam, mul_add, ← ch_add, ← ch_add,
    show i * k + k = (i + 1) * k by ring, show i * k + -k = (i - 1) * k by ring]
  exact add_comm _ _

