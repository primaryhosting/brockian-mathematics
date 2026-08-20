import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix
noncomputable def hc : ℂ := (Real.sqrt 2 : ℂ)⁻¹
/-- Hadamard. -/ noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := !![hc, hc; hc, -hc]
def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
noncomputable def PY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem H_sq : H * H = 1 := by sorry
theorem H_unitary : H * Hᴴ = 1 := by sorry
theorem H_X_H : H * PX * H = PZ := by sorry
theorem H_Z_H : H * PZ * H = PX := by sorry
theorem H_Y_H : H * PY * H = -PY := by sorry
theorem H_det : H.det = -1 := by sorry
theorem H_eq_sum : H = hc • (PX + PZ) := by sorry
end BrockianQuantum
