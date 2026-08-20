import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

open Complex Polynomial Matrix

/-- A primitive 15-th root of unity. -/

lemma adj_mul_dft : adjC15 * dftMat = dftMat * Matrix.diagonal mu := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hsum : (∑ l : Fin 15, adjC15 j l * dftMat l k)
      = ∑ l ∈ (SimpleGraph.cycleGraph 15).neighborFinset j, dftMat l k := by
    have hmv : (∑ l : Fin 15, adjC15 j l * dftMat l k)
        = (((SimpleGraph.cycleGraph 15).adjMatrix ℂ) *ᵥ (fun l => dftMat l k)) j := rfl
    rw [hmv, SimpleGraph.adjMatrix_mulVec_apply]
  rw [hsum, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one j)]
  simp only [dftMat, Matrix.of_apply, mu]
  rw [show (j - 1) * k = j * k + -k by rw [sub_mul, one_mul, sub_eq_add_neg],
    show (j + 1) * k = j * k + k by rw [add_mul, one_mul],
    zeta_add, zeta_add, ← mul_add, add_comm (zeta (-k)) (zeta k), zeta_add_neg]

