import Mathlib
/-!
# Batch 15 — single-qubit Z-rotations Rz(θ) = diag(e^{-iθ/2}, e^{iθ/2}) in SU(2). All TRUE.
-/
namespace BrockianQuantum
open Matrix
noncomputable def Rz (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-Complex.I * t / 2), 0; 0, Complex.exp (Complex.I * t / 2)]

theorem Rz_zero : Rz 0 = 1 := by sorry
theorem Rz_add (s t : ℝ) : Rz s * Rz t = Rz (s + t) := by sorry
theorem Rz_unitary (t : ℝ) : Rz t * (Rz t)ᴴ = 1 := by sorry
theorem Rz_det (t : ℝ) : (Rz t).det = 1 := by sorry
theorem Rz_conj (t : ℝ) : (Rz t)ᴴ = Rz (-t) := by sorry
theorem Rz_two_pi : Rz (2 * Real.pi) = -1 := by sorry
theorem Rz_four_pi : Rz (4 * Real.pi) = 1 := by sorry
end BrockianQuantum
