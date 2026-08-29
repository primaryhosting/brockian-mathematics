/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain comment because Lean requires `import` to precede any
-- module docstring; the identical header is repeated as the module docstring below.)

import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder

namespace Brockian

/-- The trace norm (Schatten 1-norm) of a complex square matrix `A`:
the trace of the positive semidefinite square root of `Aᴴ * A`,
i.e. the sum of the singular values of `A`. -/

theorem rot_conjTranspose_mul_self (θ : ℝ) : (rot θ)ᴴ * (rot θ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Complex.ext_iff,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The trace of `R(θ)` is `2 cos θ`. -/
