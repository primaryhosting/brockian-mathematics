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

lemma charpoly_eq : adjC15.charpoly = ∏ k : Fin 15, (X - C (mu k)) := by
  set U : (Matrix (Fin 15) (Fin 15) ℂ)ˣ := dft_isUnit.unit
  have hU : (U : Matrix (Fin 15) (Fin 15) ℂ) = dftMat := dft_isUnit.unit_spec
  have key : adjC15 = (U : Matrix (Fin 15) (Fin 15) ℂ) * Matrix.diagonal mu
      * ((U⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) : Matrix (Fin 15) (Fin 15) ℂ) := by
    calc adjC15 = adjC15 * ((U : Matrix (Fin 15) (Fin 15) ℂ) * (↑U⁻¹)) := by
          rw [U.mul_inv, mul_one]
      _ = (adjC15 * (U : Matrix (Fin 15) (Fin 15) ℂ)) * (↑U⁻¹) := (mul_assoc _ _ _).symm
      _ = _ := by rw [hU, adj_mul_dft]
  rw [key, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- **Hückel theory for the C₁₅ cycle.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₅` factors as `∏ₖ (X - 2cos(2πk/15))`, and consequently the
spectrum of the adjacency matrix is exactly `{2 cos (2πk/15) : k = 0, …, 14}`. -/
