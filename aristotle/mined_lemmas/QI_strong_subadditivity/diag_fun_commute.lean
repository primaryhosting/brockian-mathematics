import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

open scoped BigOperators ComplexOrder
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Part I: Functional calculus for Hermitian matrices -/


theorem diag_fun_commute {W : Matrix n n ℂ} {μ ν : n → ℝ} (f : ℝ → ℝ)
    (h : W * diagonal (fun i => ((μ i : ℝ) : ℂ)) = diagonal (fun i => ((ν i : ℝ) : ℂ)) * W) :
    W * diagonal (fun i => ((f (μ i) : ℝ) : ℂ)) = diagonal (fun i => ((f (ν i) : ℝ) : ℂ)) * W := by
  ext i j
  have hij : W i j * (μ j : ℂ) = W i j * (ν i : ℂ) := by
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] using this
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases eq_or_ne (W i j) 0 with hw | hw
  · simp [hw]
  · have h3 : μ j = ν i := by exact_mod_cast mul_left_cancel₀ hw hij
    rw [h3, mul_comm]

/-- Functional calculus is independent of the chosen spectral decomposition. -/
