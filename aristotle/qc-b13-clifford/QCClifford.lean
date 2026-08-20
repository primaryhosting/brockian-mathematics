import Mathlib
/-!
# Batch 13 — Clifford conjugations (H, S normalize the Pauli group). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
noncomputable def hc : ℂ := (Real.sqrt 2 : ℂ)⁻¹
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := !![hc, hc; hc, -hc]
noncomputable def S : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]
def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
noncomputable def PY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem S_Z_commute : S * PZ = PZ * S := by sorry
theorem S_conj_Y : S * PY * Sᴴ = -PX := by sorry
theorem S_conj_Z : S * PZ * Sᴴ = PZ := by sorry
theorem HS_conj_X : (H * S) * PX * (H * S)ᴴ = -PY := by sorry
theorem HS_conj_Z : (H * S) * PZ * (H * S)ᴴ = PX := by sorry
theorem H_conj_Y : H * PY * Hᴴ = -PY := by sorry
theorem S_unitary_left : Sᴴ * S = 1 := by sorry
end BrockianQuantum
