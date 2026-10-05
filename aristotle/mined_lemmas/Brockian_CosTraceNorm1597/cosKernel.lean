/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`,
-- because Lean 4 requires all `import` commands to precede any command, including a module
-- docstring. The identical text is repeated below as the module docstring.)

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace Brockian

/-- The "cosine kernel" matrix `C i j = cos (f i - g j)`. -/

noncomputable def cosKernel {n : ℕ} (f g : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (f i - g j)

/-- Absolute-value form of the Cauchy–Schwarz inequality for finite real sums,
obtained from `Real.sum_mul_le_sqrt_mul_sqrt`. -/
