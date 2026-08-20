import Mathlib
/-!
# Batch 6 — GHZ / W three-qubit states and their stabilizers. All TRUE; bare `import Mathlib`.
Basis |b0 b1 b2> indexed 0..7. XXX = X⊗X⊗X (anti-diagonal, i+j=7). Z-stabilizers are diagonal
with signs (-1)^(sum of the two Z-bits).
-/
namespace BrockianQuantum
open Matrix

theorem normSq_dd : Complex.normSq dd = 1/3 := by
  have h : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [dd, ← Complex.ofReal_inv, Complex.normSq_ofReal, ← mul_inv, h]
  norm_num

