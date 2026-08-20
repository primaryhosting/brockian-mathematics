import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open scoped Matrix

/-! ### A primitive 14-th root of unity and the associated character -/

/-- A primitive 14-th root of unity. -/

theorem adj_mul_Fm :
    (SimpleGraph.cycleGraph 14).adjMatrix ℂ * Fm = Fm * Dm := by
  ext j l
  rw [SimpleGraph.adjMatrix_mul_apply, SimpleGraph.cycleGraph_neighborFinset (n := 12)]
  have hne : (j - 1 : Fin 14) ≠ j + 1 := by
    intro h
    have h2 : j = j + (1 + 1) := by
      rw [← add_assoc]
      exact sub_eq_iff_eq_add.mp h
    have h3 : (0 : Fin 14) = 1 + 1 := by
      nth_rewrite 1 [show j = j + 0 from (add_zero j).symm] at h2
      exact add_left_cancel h2
    exact absurd h3 (by decide)
  rw [Finset.sum_pair hne, Fm_succ, Fm_pred]
  have hD : (Fm * Dm) j l = Fm j l * (lam l : ℂ) := by
    simp [Matrix.mul_apply, Dm, Matrix.diagonal_apply, Finset.sum_ite_eq']
  rw [hD, ← ee_add_ee_neg l]
  ring

