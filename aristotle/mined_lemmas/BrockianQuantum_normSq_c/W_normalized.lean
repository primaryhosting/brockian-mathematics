import Mathlib
/-!
# Batch 6 — GHZ / W three-qubit states and their stabilizers. All TRUE; bare `import Mathlib`.
Basis |b0 b1 b2> indexed 0..7. XXX = X⊗X⊗X (anti-diagonal, i+j=7). Z-stabilizers are diagonal
with signs (-1)^(sum of the two Z-bits).
-/
namespace BrockianQuantum
open Matrix

theorem W_normalized : ∑ i, Complex.normSq (Wst i) = 1 := by
  simp [Wst, Fin.sum_univ_eight, normSq_dd]
  norm_num

