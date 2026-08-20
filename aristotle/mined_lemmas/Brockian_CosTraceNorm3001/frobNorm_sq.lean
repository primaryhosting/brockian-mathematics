/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

open Matrix

variable {n : ℕ}

/-- The Frobenius (Hilbert–Schmidt) inner product of two real matrices, written as a
trace, is the sum of the entrywise products. -/

lemma frobNorm_sq (A : Matrix (Fin n) (Fin n) ℝ) :
    frobNorm A ^ 2 = trace (Aᵀ * A) :=
  Real.sq_sqrt (trace_transpose_self_nonneg A)

/-- Cauchy–Schwarz for the Frobenius inner product of real matrices. -/
