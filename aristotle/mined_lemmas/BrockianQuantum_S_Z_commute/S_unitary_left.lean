import Mathlib
/-!
# Batch 13 — Clifford conjugations (H, S normalize the Pauli group). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

theorem S_unitary_left : Sᴴ * S = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, S, Matrix.conjTranspose_apply]

end BrockianQuantum

