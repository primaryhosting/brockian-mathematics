import Mathlib
/-!
# Batch 5 — Bell states as stabilizer eigenvectors. All TRUE; bare `import Mathlib`.
Basis order |00>,|01>,|10>,|11> = 0,1,2,3.  XX = X⊗X, ZZ = Z⊗Z.
-/
namespace BrockianQuantum
open Matrix

theorem phiM_ZZ_eigen : ZZ.mulVec phiM = phiM := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, ZZ, phiM, dotProduct, Fin.sum_univ_four]

