import Mathlib
/-!
# Batch 6 — GHZ / W three-qubit states and their stabilizers. All TRUE; bare `import Mathlib`.
Basis |b0 b1 b2> indexed 0..7. XXX = X⊗X⊗X (anti-diagonal, i+j=7). Z-stabilizers are diagonal
with signs (-1)^(sum of the two Z-bits).
-/
namespace BrockianQuantum
open Matrix

theorem GHZ_XXX_eigen : XXX.mulVec GHZ = GHZ := by
  funext i
  fin_cases i <;>
    simp [XXX, GHZ, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

