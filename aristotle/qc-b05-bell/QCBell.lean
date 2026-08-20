import Mathlib
/-!
# Batch 5 — Bell states as stabilizer eigenvectors. All TRUE; bare `import Mathlib`.
Basis order |00>,|01>,|10>,|11> = 0,1,2,3.  XX = X⊗X, ZZ = Z⊗Z.
-/
namespace BrockianQuantum
open Matrix
noncomputable def c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
def XX : Matrix (Fin 4) (Fin 4) ℂ := !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]
def ZZ : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0; 0,-1,0,0; 0,0,-1,0; 0,0,0,1]
noncomputable def phiP : Fin 4 → ℂ := ![c, 0, 0, c]
noncomputable def phiM : Fin 4 → ℂ := ![c, 0, 0, -c]
noncomputable def psiP : Fin 4 → ℂ := ![0, c, c, 0]
noncomputable def psiM : Fin 4 → ℂ := ![0, c, -c, 0]

theorem phiP_XX_eigen : XX.mulVec phiP = phiP := by sorry
theorem phiP_ZZ_eigen : ZZ.mulVec phiP = phiP := by sorry
theorem psiP_XX_eigen : XX.mulVec psiP = psiP := by sorry
theorem phiM_ZZ_eigen : ZZ.mulVec phiM = phiM := by sorry
theorem psiM_ZZ_eigen : ZZ.mulVec psiM = -psiM := by sorry
theorem phiP_normalized : ∑ i, Complex.normSq (phiP i) = 1 := by sorry
theorem phiP_psiP_orthogonal : ∑ i, (starRingEnd ℂ) (phiP i) * psiP i = 0 := by sorry
end BrockianQuantum
