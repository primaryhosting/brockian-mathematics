import Mathlib
/-!
# Batch 3 — phase gates S, T (Clifford+T). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem S_sq_eq_Z : S * S = PZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, PZ, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

