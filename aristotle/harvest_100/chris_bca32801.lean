import Mathlib

/-!
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
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

namespace Riemann
namespace Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ` (0-indexed): the entry in row `i`, column `j`
is `1` when `j = 0` or when `i + 1` divides `j + 1`, and `0` otherwise. -/
def R5 : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then (1 : ℤ) else 0

/-- Explicit entries of the `5 × 5` Redheffer matrix. -/
lemma R5_eq :
    R5 = !![1, 1, 1, 1, 1;
            1, 1, 0, 1, 0;
            1, 0, 1, 0, 0;
            1, 0, 0, 1, 0;
            1, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [R5]

/-- The unitriangular lower factor used in the LU decomposition of the row-swapped
Redheffer matrix. -/
def L5 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, 0, 0, 0, 0;
     -1, 1, 0, 0, 0;
     -1, 0, 1, 0, 0;
     1, -1, -1, 1, 0;
     1, -1, -1, 0, 1]

/-- The upper triangular factor obtained from Gaussian elimination. -/
def U5 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, 1, 1, 1, 1;
     0, -1, 0, -1, -1;
     0, 0, -1, 0, -1;
     0, 0, 0, 1, 1;
     0, 0, 0, 0, 2]

lemma det_L5 : L5.det = 1 := by
  rw [← Matrix.det_transpose]
  have h : L5.transpose = !![1, -1, -1, 1, 1;
                      0, 1, 0, -1, -1;
                      0, 0, 1, -1, -1;
                      0, 0, 0, 1, 0;
                      0, 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [L5]
  rw [h, Matrix.det_of_upperTriangular]
  · simp [Fin.prod_univ_five]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

lemma det_U5 : U5.det = 2 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [U5, Fin.prod_univ_five]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [U5]

/-- Gaussian elimination: multiplying the row-swapped Redheffer matrix by `L5`
yields the upper triangular matrix `U5`. -/
lemma L5_mul_swap : L5 * (R5.submatrix (Equiv.swap 1 2) id) = U5 := by
  rw [R5_eq]
  have h : ((!![1, 1, 1, 1, 1;
                1, 1, 0, 1, 0;
                1, 0, 1, 0, 0;
                1, 0, 0, 1, 0;
                1, 0, 0, 0, 1] : Matrix (Fin 5) (Fin 5) ℤ).submatrix (Equiv.swap 1 2) id) =
      !![1, 1, 1, 1, 1;
         1, 0, 1, 0, 0;
         1, 1, 0, 1, 0;
         1, 0, 0, 1, 0;
         1, 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Equiv.swap_apply_def]
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L5, U5, Matrix.mul_apply, Fin.sum_univ_five]

/-- The determinant of the `5 × 5` Redheffer matrix equals the Mertens function value
`M(5) = μ(1) + μ(2) + μ(3) + μ(4) + μ(5) = 1 - 1 - 1 + 0 - 1 = -2`. -/
theorem det_eq_mertens_5 : R5.det = -2 := by
  have hswap : (R5.submatrix (Equiv.swap (1 : Fin 5) 2) id).det = -R5.det := by
    rw [Matrix.det_permute]
    rw [Equiv.Perm.sign_swap (by decide)]
    simp
  have hdet : L5.det * (R5.submatrix (Equiv.swap (1 : Fin 5) 2) id).det = U5.det := by
    rw [← Matrix.det_mul, L5_mul_swap]
  rw [det_L5, det_U5, one_mul, hswap] at hdet
  linarith

/-- The determinant of the `5 × 5` Redheffer matrix agrees with the sum of the Möbius
function over `1, …, 5`. -/
theorem det_eq_mertens_5' :
    R5.det = ∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n : ℤ) := by
  have h1 : (ArithmeticFunction.moebius 1 : ℤ) = 1 := ArithmeticFunction.moebius_apply_one
  have h2 : (ArithmeticFunction.moebius 2 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h3 : (ArithmeticFunction.moebius 3 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h4 : (ArithmeticFunction.moebius 4 : ℤ) = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  have h5 : (ArithmeticFunction.moebius 5 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  rw [det_eq_mertens_5, show Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) from by decide]
  simp [h1, h2, h3, h4, h5]

end Redheffer
end Riemann

