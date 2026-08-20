import Mathlib
/-!
# Batch 3 — phase gates S, T (Clifford+T). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem S_unitary : S * Sᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

