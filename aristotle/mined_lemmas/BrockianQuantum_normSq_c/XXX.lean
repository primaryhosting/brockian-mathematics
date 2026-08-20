import Mathlib
/-!
# Batch 6 — GHZ / W three-qubit states and their stabilizers. All TRUE; bare `import Mathlib`.
Basis |b0 b1 b2> indexed 0..7. XXX = X⊗X⊗X (anti-diagonal, i+j=7). Z-stabilizers are diagonal
with signs (-1)^(sum of the two Z-bits).
-/
namespace BrockianQuantum
open Matrix

def XXX : Matrix (Fin 8) (Fin 8) ℂ := fun i j => if (i : ℕ) + (j : ℕ) = 7 then 1 else 0
