import Mathlib
/-!
# Batch 8 — discrete/quantum Fourier transform (concrete 2- and 4-point). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
/-- 2-point DFT (unnormalized) = √2 · Hadamard. -/

theorem W4_row0 : ∀ k, W4 0 k = 1 := by
  intro k
  fin_cases k <;> simp [W4]
