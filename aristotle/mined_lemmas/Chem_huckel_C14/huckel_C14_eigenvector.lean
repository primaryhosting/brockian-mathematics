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

theorem huckel_C14_eigenvector (k : Fin 14) :
    (fun j : Fin 14 => Fm j k) ≠ 0 ∧
      (SimpleGraph.cycleGraph 14).adjMatrix ℂ *ᵥ (fun j : Fin 14 => Fm j k) =
        ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 14) : ℝ) : ℂ) • (fun j : Fin 14 => Fm j k) := by
  constructor
  · intro h
    have h0 : Fm 0 k = 0 := congrFun h 0
    rw [Fm] at h0
    exact ee_ne_zero _ h0
  · funext j
    have h := congrFun (congrFun adj_mul_Fm j) k
    simp only [Matrix.mul_apply] at h
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [h]
    simp only [Dm, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [lam]
    ring

end Chem

