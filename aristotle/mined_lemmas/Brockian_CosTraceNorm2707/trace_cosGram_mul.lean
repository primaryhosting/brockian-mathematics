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
