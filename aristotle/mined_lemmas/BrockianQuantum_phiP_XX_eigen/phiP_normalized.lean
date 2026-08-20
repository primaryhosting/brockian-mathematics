import Mathlib
/-!
# Batch 5 — Bell states as stabilizer eigenvectors. All TRUE; bare `import Mathlib`.
Basis order |00>,|01>,|10>,|11> = 0,1,2,3.  XX = X⊗X, ZZ = Z⊗Z.
-/
namespace BrockianQuantum
open Matrix

theorem phiP_normalized : ∑ i, Complex.normSq (phiP i) = 1 := by
  have hc : Complex.normSq c = 1 / 2 := by simp [c]
  simp [Fin.sum_univ_four, phiP, hc]
  norm_num

