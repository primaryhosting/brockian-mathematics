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

theorem cos_kernel_posSemidef (n : ℕ) (x : Fin n → ℝ) : (cosKernel n x).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp [cosKernel, Matrix.conjTranspose_apply, ← Real.cos_neg (x i - x j)]
  · rw [star_trivial, cos_kernel_dotProduct, cos_kernel_quadratic_form]
    positivity

/-- The trace of the cosine kernel matrix is `n`, since its diagonal entries are all `cos 0 = 1`. -/
