/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
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

open Polynomial

/-- The Hückel (adjacency) matrix of the carbon skeleton of cyclobutadiene `C₄`,
i.e. the adjacency matrix of the cycle graph `C₄`, with coefficients in `R`. -/
noncomputable def C4Matrix (R : Type*) [Semiring R] : Matrix (Fin 4) (Fin 4) R :=
  (SimpleGraph.cycleGraph 4).adjMatrix R

/-- The `k`-th Hückel eigenvalue of `C₄`: `2 cos (2πk/4)`. -/
noncomputable def huckelEigenvalue (k : Fin 4) : ℝ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 4)

/-- The `k`-th Hückel eigenvector (discrete Fourier mode) of `C₄`:
`j ↦ exp (2πi·k·j/4)`. -/
noncomputable def huckelVector (k : Fin 4) : Fin 4 → ℂ :=
  fun j => Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * (j : ℕ)) / 4)

/-- Explicit form of the adjacency matrix of `C₄`. -/
theorem C4Matrix_eq (R : Type*) [Semiring R] :
    C4Matrix R = !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
      | (rw [C4Matrix, SimpleGraph.adjMatrix_apply, if_pos (by decide)]; simp)
      | (rw [C4Matrix, SimpleGraph.adjMatrix_apply, if_neg (by decide)]; simp)

/-- Determinant of a general `4 × 4` matrix by cofactor expansion along the first row. -/
theorem det_fin_four {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
          - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
          + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
    - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
          - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
          + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
    + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
          - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
          + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
    - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)
          - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
          + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- The characteristic polynomial of the `C₄` adjacency matrix is `X⁴ - 4X²`. -/
theorem C4Matrix_charpoly : (C4Matrix ℝ).charpoly = X ^ 4 - 4 * X ^ 2 := by
  rw [C4Matrix_eq, Matrix.charpoly, det_fin_four]
  simp [Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne]
  ring

/-- The four Hückel eigenvalues of `C₄` are `2, 0, -2, 0`. -/
theorem huckelEigenvalue_eq (k : Fin 4) : huckelEigenvalue k = ![2, 0, -2, 0] k := by
  unfold huckelEigenvalue
  fin_cases k
  · show (2 : ℝ) * Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) / 4) = 2
    norm_num
  · show (2 : ℝ) * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / 4) = 0
    rw [show (2 * Real.pi * ((1 : ℕ) : ℝ) / 4) = Real.pi / 2 by push_cast; ring]
    simp
  · show (2 : ℝ) * Real.cos (2 * Real.pi * ((2 : ℕ) : ℝ) / 4) = -2
    rw [show (2 * Real.pi * ((2 : ℕ) : ℝ) / 4) = Real.pi by push_cast; ring]
    simp
  · show (2 : ℝ) * Real.cos (2 * Real.pi * ((3 : ℕ) : ℝ) / 4) = 0
    rw [show (2 * Real.pi * ((3 : ℕ) : ℝ) / 4) = Real.pi + Real.pi / 2 by push_cast; ring]
    simp [Real.cos_add]

/-- The product of the linear factors `X - 2cos(2πk/4)` is `X⁴ - 4X²`. -/
theorem huckel_prod_eq : (∏ k : Fin 4, (X - C (huckelEigenvalue k))) = (X : ℝ[X]) ^ 4 - 4 * X ^ 2 := by
  simp only [huckelEigenvalue_eq, Fin.prod_univ_four]
  norm_num [C_ofNat, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  ring

/-- The Hückel eigenvector components are powers of `i`. -/
theorem huckelVector_eq (k j : Fin 4) : huckelVector k j = Complex.I ^ ((k : ℕ) * (j : ℕ)) := by
  rw [huckelVector, show (2 * (Real.pi : ℂ) * Complex.I * ((k : ℕ) * (j : ℕ)) / 4)
      = (((k : ℕ) * (j : ℕ) : ℕ) : ℂ) * (Real.pi / 2 * Complex.I) by push_cast; ring,
    Complex.exp_nat_mul]
  norm_num [Complex.exp_mul_I]

/-- Each Hückel mode is a nonzero vector. -/
theorem huckelVector_ne_zero (k : Fin 4) : huckelVector k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [huckelVector_eq] at h0
  simp at h0

/-- Each Hückel mode is an eigenvector of the `C₄` adjacency matrix with eigenvalue
`2 cos (2πk/4)`. -/
theorem C4Matrix_mulVec_huckelVector (k : Fin 4) :
    (C4Matrix ℂ).mulVec (huckelVector k) = ((huckelEigenvalue k : ℝ) : ℂ) • huckelVector k := by
  funext i
  rw [C4Matrix_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, huckelVector_eq, huckelEigenvalue_eq,
    Pi.smul_apply, smul_eq_mul]
  fin_cases k <;> fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, pow_succ,
      Complex.I_sq]

/-- **Hückel theory for cyclobutadiene (C₄).**
The adjacency eigenvalues of the cycle graph `C₄` are exactly `2 cos (2πk/4)` for `k = 0,1,2,3`:

* the characteristic polynomial of the adjacency matrix factors as
  `∏ k, (X - 2 cos (2πk/4))`, so these are the eigenvalues with multiplicity;
* each Fourier mode `j ↦ exp (2πi k j / 4)` is a nonzero eigenvector with eigenvalue
  `2 cos (2πk/4)`. -/
theorem huckel_C4 :
    (C4Matrix ℝ).charpoly = ∏ k : Fin 4, (X - C (huckelEigenvalue k)) ∧
    ∀ k : Fin 4, huckelVector k ≠ 0 ∧
      (C4Matrix ℂ).mulVec (huckelVector k) = ((huckelEigenvalue k : ℝ) : ℂ) • huckelVector k := by
  refine ⟨?_, fun k => ⟨huckelVector_ne_zero k, C4Matrix_mulVec_huckelVector k⟩⟩
  rw [C4Matrix_charpoly, huckel_prod_eq]

end Chem

