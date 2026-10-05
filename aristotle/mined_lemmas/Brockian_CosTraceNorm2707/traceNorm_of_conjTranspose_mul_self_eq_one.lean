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

theorem traceNorm_of_conjTranspose_mul_self_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : Aᴴ * A = 1) : traceNorm A = Fintype.card n := by
  unfold traceNorm
  rw [h, CFC.sqrt_one]
  simp

/-- If `Aᴴ * A = 1` then every diagonal entry of `A` has norm at most `1`. -/
