import Mathlib
/-!
# Batch 13 — Clifford conjugations (H, S normalize the Pauli group). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

noncomputable def S : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]

def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem S_Z_commute : S * PZ = PZ * S := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, S, PZ]
