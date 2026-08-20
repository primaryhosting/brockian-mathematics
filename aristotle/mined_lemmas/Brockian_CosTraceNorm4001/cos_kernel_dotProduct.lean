import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module doc comment, so the header
-- block above sits immediately after the single `import Mathlib` line.)

open scoped BigOperators
open scoped Real
open scoped Matrix

set_option maxRecDepth 10000

namespace Brockian

/-- The cosine kernel matrix `C i j = cos (x i - x j)` attached to a family of phases `x`. -/

theorem cos_kernel_dotProduct (n : ℕ) (x v : Fin n → ℝ) :
    v ⬝ᵥ (cosKernel n x *ᵥ v) = ∑ i, ∑ j, v i * v j * Real.cos (x i - x j) := by
  simp only [dotProduct, cosKernel, Matrix.mulVec, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The cosine kernel matrix is positive semidefinite. -/
