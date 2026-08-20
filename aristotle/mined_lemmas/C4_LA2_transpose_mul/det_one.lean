import Mathlib
namespace C4.LA2
open Matrix

theorem det_one {n : ℕ} : (1 : Matrix (Fin n) (Fin n) ℝ).det = 1 := Matrix.det_one
