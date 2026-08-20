import Mathlib
/-!
# Batch 3 — phase gates S, T (Clifford+T). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem S_pow_four : S ^ 4 = 1 := by
  have h : S ^ 4 = (S * S) * (S * S) := by noncomm_ring
  rw [h, S_sq_eq_Z]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PZ, Matrix.mul_apply, Fin.sum_univ_two]

