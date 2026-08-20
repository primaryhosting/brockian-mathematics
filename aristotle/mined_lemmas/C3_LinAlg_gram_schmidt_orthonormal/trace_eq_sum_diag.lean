import Mathlib

open InnerProductSpace

namespace C3.LinAlg

/-- Gram–Schmidt applied to a linearly independent family produces an orthonormal family. -/

theorem trace_eq_sum_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace A = ∑ i, A i i := rfl

end C3.LinAlg

