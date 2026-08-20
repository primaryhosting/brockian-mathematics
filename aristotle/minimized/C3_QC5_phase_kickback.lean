import Mathlib
open Matrix
namespace C3.QC5

def X : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

/-- The Pauli-`X` gate fixes the (unnormalised) `|+⟩` state.
Type ascription added to the right-hand-side matrix literal so that it
elaborates over `ℂ` rather than `ℕ`. -/

theorem phase_kickback : X * (!![1;1] : Matrix (Fin 2) (Fin 1) ℂ) = !![1;1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Matrix.mul_apply, Fin.sum_univ_two]
