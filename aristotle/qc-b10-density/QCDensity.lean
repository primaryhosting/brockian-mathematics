import Mathlib
/-!
# Batch 10 — density matrices, projectors, Pauli traces. All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
def P0 : Matrix (Fin 2) (Fin 2) ℂ := !![1,0; 0,0]
def P1 : Matrix (Fin 2) (Fin 2) ℂ := !![0,0; 0,1]
def Dplus : Matrix (Fin 2) (Fin 2) ℂ := !![1/2,1/2; 1/2,1/2]
def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0,1; 1,0]
def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1,0; 0,-1]

theorem P0_idem : P0 * P0 = P0 := by sorry
theorem P0_trace_one : Matrix.trace P0 = 1 := by sorry
theorem completeness : P0 + P1 = 1 := by sorry
theorem P0_P1_orthogonal : P0 * P1 = 0 := by sorry
theorem Dplus_idem : Dplus * Dplus = Dplus := by sorry
theorem PX_traceless : Matrix.trace PX = 0 := by sorry
theorem PX_PZ_traceless : Matrix.trace (PX * PZ) = 0 := by sorry
end BrockianQuantum
