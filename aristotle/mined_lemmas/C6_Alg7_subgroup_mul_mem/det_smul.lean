import Mathlib
namespace C6.Alg7


theorem det_smul {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : (c • A).det = c^n * A.det := by
  simp

end C6.Alg7

