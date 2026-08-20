/- (module docstrings may not precede `import`, so the required header is kept
   verbatim inside this comment block)
/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The cosine Gram matrix of a family of angles: `C i j = cos (x i - x j)`.
It is the Gram matrix of the unit vectors `(cos (x i), sin (x i))`, hence positive
semidefinite of rank at most `2`. -/
noncomputable def cosGram {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (x i - x j)

/-- A rank-one quadratic bound: if `U` is a contraction (in the elementary,
coordinatewise form `‖U w‖² ≤ ‖w‖²`), then `|⟪u, U u⟫| ≤ ‖u‖²`. -/
lemma abs_quadratic_le_of_contraction {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : ∀ w : Fin n → ℝ, ∑ i, (∑ j, U i j * w j) ^ 2 ≤ ∑ i, (w i) ^ 2)
    (u : Fin n → ℝ) :
    |∑ j, u j * ∑ i, U j i * u i| ≤ ∑ i, (u i) ^ 2 := by
  set A : ℝ := ∑ i, (u i) ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hCS : (∑ j, u j * ∑ i, U j i * u i) ^ 2 ≤ A * ∑ j, (∑ i, U j i * u i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hUu : ∑ j, (∑ i, U j i * u i) ^ 2 ≤ A := hU u
  have hsq : (∑ j, u j * ∑ i, U j i * u i) ^ 2 ≤ A ^ 2 := by
    have := mul_le_mul_of_nonneg_left hUu hA0
    nlinarith [hCS]
  rw [abs_le]
  constructor <;> nlinarith [hsq, hA0]

/-- The trace of the cosine Gram matrix is `n`. -/
lemma trace_cosGram {n : ℕ} (x : Fin n → ℝ) : Matrix.trace (cosGram x) = n := by
  simp [cosGram, Matrix.trace, Matrix.diag]

/-- Expansion of `tr (C U)` for the cosine Gram matrix into its two rank-one pieces. -/
lemma trace_cosGram_mul {n : ℕ} (x : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (cosGram x * U) =
      (∑ j, Real.cos (x j) * ∑ i, U j i * Real.cos (x i)) +
      (∑ j, Real.sin (x j) * ∑ i, U j i * Real.sin (x i)) := by
  have h1 : Matrix.trace (cosGram x * U) = ∑ i, ∑ j, cosGram x i j * U j i := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diag]
  rw [h1, Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cosGram, Matrix.of_apply, Real.cos_sub]
  ring

/-- **Cos Trace Norm 2707.**
For any angles `x : Fin n → ℝ`, let `C i j = cos (x i - x j)` be the cosine Gram matrix.
Then for every contraction `U` (i.e. `‖U w‖² ≤ ‖w‖²` for all `w`) one has
`|tr (C U)| ≤ n`, and the value `n` is attained at `U = 1`.
Since the trace norm satisfies `‖C‖₁ = sup { |tr (C U)| : ‖U‖ ≤ 1 }`, this says exactly
that the trace norm of the cosine Gram matrix equals `n`. -/
theorem CosTraceNorm2707 {n : ℕ} (x : Fin n → ℝ) :
    (∀ U : Matrix (Fin n) (Fin n) ℝ,
        (∀ w : Fin n → ℝ, ∑ i, (∑ j, U i j * w j) ^ 2 ≤ ∑ i, (w i) ^ 2) →
        |Matrix.trace (cosGram x * U)| ≤ n) ∧
      Matrix.trace (cosGram x * (1 : Matrix (Fin n) (Fin n) ℝ)) = n := by
  constructor
  · intro U hU
    rw [trace_cosGram_mul]
    refine (abs_add_le _ _).trans ?_
    have hc := abs_quadratic_le_of_contraction U hU (fun i => Real.cos (x i))
    have hs := abs_quadratic_le_of_contraction U hU (fun i => Real.sin (x i))
    have hsum : (∑ i, (Real.cos (x i)) ^ 2) + (∑ i, (Real.sin (x i)) ^ 2) = n := by
      rw [← Finset.sum_add_distrib]
      simp [Real.cos_sq_add_sin_sq]
    linarith [hc, hs]
  · rw [mul_one, trace_cosGram]

end Brockian
