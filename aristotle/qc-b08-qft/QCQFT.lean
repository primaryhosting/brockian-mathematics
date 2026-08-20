import Mathlib
/-!
# Batch 8 — discrete/quantum Fourier transform (concrete 2- and 4-point). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
/-- 2-point DFT (unnormalized) = √2 · Hadamard. -/
def W2 : Matrix (Fin 2) (Fin 2) ℂ := !![1,1; 1,-1]
/-- 4-point DFT, entries i^{jk}. -/
noncomputable def W4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,1; 1,Complex.I,-1,-Complex.I; 1,-1,1,-1; 1,-Complex.I,-1,Complex.I]
/-- DFT² parity-reversal support. -/
def P4 : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0; 0,0,0,1; 0,0,1,0; 0,1,0,0]

theorem W2_unitary : W2 * W2ᴴ = (2 : ℂ) • 1 := by sorry
theorem W2_sq : W2 * W2 = (2 : ℂ) • 1 := by sorry
theorem W2_det : W2.det = -2 := by sorry
theorem W4_symmetric : W4ᵀ = W4 := by sorry
theorem W4_row0 : ∀ k, W4 0 k = 1 := by sorry
theorem W4_unitary : W4 * W4ᴴ = (4 : ℂ) • 1 := by sorry
theorem W4_sq_reversal : W4 * W4 = (4 : ℂ) • P4 := by sorry
end BrockianQuantum
