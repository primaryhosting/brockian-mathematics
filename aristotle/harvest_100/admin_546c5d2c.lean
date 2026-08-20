import Mathlib

/-!
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
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

namespace Riemann.Redheffer

/-- The `6 × 6` Redheffer matrix: with `Fin 6` indices `i, j` standing for the
divisor `i + 1` and the integer `j + 1`, the entry is `1` when `j = 0`
(the first column) or when `i + 1` divides `j + 1`, and `0` otherwise. -/
def R : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- Explicit entries of the `6 × 6` Redheffer matrix. -/
theorem R_eq :
    R = !![1, 1, 1, 1, 1, 1;
           1, 1, 0, 1, 0, 1;
           1, 0, 1, 0, 0, 1;
           1, 0, 0, 1, 0, 0;
           1, 0, 0, 0, 1, 0;
           1, 0, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R]

/-- The unipotent column-operation matrix: multiplying on the right by `E`
replaces the first column of `R` by a suitable integer combination of all the
columns, clearing every entry below the top-left corner. -/
def E : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 1, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0;
     -1, 0, 0, 1, 0, 0;
     -1, 0, 0, 0, 1, 0;
     -1, 0, 0, 0, 0, 1]

/-- The upper triangular matrix obtained from `R` by the column operation `E`. -/
def T : Matrix (Fin 6) (Fin 6) ℤ :=
  !![-1, 1, 1, 1, 1, 1;
      0, 1, 0, 1, 0, 1;
      0, 0, 1, 0, 0, 1;
      0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1]

theorem R_mul_E : R * E = T := by
  rw [R_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, E, T]

theorem det_E : E.det = 1 := by
  rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular]
  · simp [Fin.prod_univ_six, E]
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [E]

theorem det_T : T.det = -1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [Fin.prod_univ_six, T]
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [T]

/-- The determinant of the `6 × 6` Redheffer matrix equals the Mertens value
`M(6) = -1`. -/
theorem det_eq_mertens_6 : R.det = -1 := by
  have h := congrArg Matrix.det R_mul_E
  rwa [Matrix.det_mul, det_E, det_T, mul_one] at h

end Riemann.Redheffer

