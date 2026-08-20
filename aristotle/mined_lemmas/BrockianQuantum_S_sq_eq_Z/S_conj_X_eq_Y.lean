import Mathlib
/-!
# Batch 3 — phase gates S, T (Clifford+T). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem S_conj_X_eq_Y : S * PX * Sᴴ = PY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, PX, PY, Matrix.mul_apply, Fin.sum_univ_two]
end BrockianQuantum

