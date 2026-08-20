import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

lemma four_norm_bound {n : ℕ} (p q r s : ℝ)
    (h1 : p ^ 2 + q ^ 2 = n) (h2 : r ^ 2 + s ^ 2 = n) : p * r + q * s ≤ n := by
  nlinarith [sq_nonneg (p * s - q * r), sq_nonneg (p * r + q * s),
    Nat.cast_nonneg (α := ℝ) n]

/-! ## The trace-norm bounds -/

/-- **Trace-norm bound for the cosine matrix.**  For any phases `x, y : Fin n → ℝ`, the
matrix with entries `cos (x i - y j)` has trace norm at most `n`. -/
