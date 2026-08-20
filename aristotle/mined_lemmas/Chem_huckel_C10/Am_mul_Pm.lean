import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

attribute [local instance] Fin.instCommRing

/-! ### A primitive 10-th root of unity -/

/-- The primitive 10-th root of unity `exp (2πi/10)`. -/

lemma Am_mul_Pm : Am * Pm = Pm * Matrix.diagonal Dv := by
  ext j l
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have : ∀ k : Fin 10, Am j k * Pm k l =
      (if k = j - 1 then E (k * l) else 0) + (if k = j + 1 then E (k * l) else 0) := by
    intro k
    rw [Am_apply]
    simp only [Pm]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j - 1) (fun k => E (k * l)),
    Finset.sum_ite_eq' Finset.univ (j + 1) (fun k => E (k * l))]
  simp only [Finset.mem_univ, if_true]
  simp only [Pm, Dv]
  have e1 : ((j - 1) * l : Fin 10) = j * l + (-l) := by ring
  have e2 : ((j + 1) * l : Fin 10) = j * l + l := by ring
  rw [e1, e2, E_add, E_add]
  ring

