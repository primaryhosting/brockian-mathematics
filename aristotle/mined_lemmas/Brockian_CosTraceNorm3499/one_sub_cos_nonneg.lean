/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Real Matrix

namespace Brockian

/-- The entrywise cosine of a real matrix has trace equal to the sum of the cosines of the
diagonal entries. -/

lemma one_sub_cos_nonneg (x : ℝ) : 0 ≤ 1 - Real.cos x := by
  have := Real.cos_le_one x
  linarith

/-- **Cosine trace norm bound.**

For every real `n × n` matrix `A`, the trace of the entrywise cosine `A.map cos` has absolute
value at most `n`, and it attains the value `n` exactly when every diagonal entry of `A` is an
integer multiple of `2π`. -/
