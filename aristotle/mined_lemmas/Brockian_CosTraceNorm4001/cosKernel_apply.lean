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

@[simp] theorem cosKernel_apply (n : ℕ) (x : Fin n → ℝ) (i j : Fin n) :
    cosKernel n x i j = Real.cos (x i - x j) := rfl

/-- The quadratic form of the cosine kernel matrix is a sum of two squares: the kernel is the
Gram matrix of the unit vectors `(cos (x i), sin (x i))`. -/
