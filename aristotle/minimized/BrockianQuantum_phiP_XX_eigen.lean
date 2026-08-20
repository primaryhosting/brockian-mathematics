import Mathlib
/-!
# Batch 5 — Bell states as stabilizer eigenvectors. All TRUE; bare `import Mathlib`.
Basis order |00>,|01>,|10>,|11> = 0,1,2,3.  XX = X⊗X, ZZ = Z⊗Z.
-/
namespace BrockianQuantum
open Matrix

noncomputable def c : ℂ := (Real.sqrt 2 : ℂ)⁻¹

def XX : Matrix (Fin 4) (Fin 4) ℂ := !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]

noncomputable def phiP : Fin 4 → ℂ := ![c, 0, 0, c]

theorem phiP_XX_eigen : XX.mulVec phiP = phiP := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, XX, phiP, dotProduct, Fin.sum_univ_four]
