import Mathlib
namespace C4.LA2
open Matrix

theorem transpose_mul {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ) :
    (A*B)ᵀ = Bᵀ * Aᵀ := Matrix.transpose_mul A B
