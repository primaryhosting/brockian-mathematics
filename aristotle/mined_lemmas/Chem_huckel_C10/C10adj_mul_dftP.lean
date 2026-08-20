/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/

lemma C10adj_mul_dftP : C10adj * dftP = dftP * eigDiag := by
  ext j k
  have hP : ∀ i : Fin 10, dftP i k = (w ^ (k : ℕ)) ^ (i : ℕ) := by
    intro i
    simp only [dftP, Matrix.of_apply]
    rw [← pow_mul, Nat.mul_comm]
  have hz : (w ^ (k : ℕ)) ^ 10 = 1 := w_pow_mul_ten (k : ℕ)
  rw [Matrix.mul_apply, eigDiag, Matrix.mul_diagonal, hP, huckelEigenvalue_eq]
  simp only [hP]
  set z : ℂ := w ^ (k : ℕ) with hzdef
  clear_value z
  clear hP hzdef
  fin_cases j <;>
    simp +decide [C10adj, SimpleGraph.adjMatrix_apply, Fin.sum_univ_succ]
  · linear_combination -hz
  · linear_combination -z * hz
  · linear_combination -z ^ 2 * hz
  · linear_combination -z ^ 3 * hz
  · linear_combination -z ^ 4 * hz
  · linear_combination -z ^ 5 * hz
  · linear_combination -z ^ 6 * hz
  · linear_combination -z ^ 7 * hz
  · linear_combination -(1 + z ^ 8) * hz

/-- The unit of the matrix algebra given by the DFT matrix. -/
