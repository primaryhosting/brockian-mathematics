import Mathlib
/-!
# Batch 5 — Bell states as stabilizer eigenvectors. All TRUE; bare `import Mathlib`.
Basis order |00>,|01>,|10>,|11> = 0,1,2,3.  XX = X⊗X, ZZ = Z⊗Z.
-/
namespace BrockianQuantum
open Matrix

theorem phiP_psiP_orthogonal : ∑ i, (starRingEnd ℂ) (phiP i) * psiP i = 0 := by
  simp [Fin.sum_univ_four, phiP, psiP]

end BrockianQuantum

