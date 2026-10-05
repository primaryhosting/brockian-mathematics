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

noncomputable def traceNorm {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  (CFC.sqrt (Aᴴ * A)).trace.re

/-- If the columns of `A` are orthonormal (`Aᴴ * A = 1`), then all singular values of `A`
equal `1`, so the trace norm is the size of the matrix. -/
