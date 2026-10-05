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

lemma sum_cos_sq_add_sum_sin_sq {n : ℕ} (f : Fin n → ℝ) :
    (∑ i, Real.cos (f i) ^ 2) + (∑ i, Real.sin (f i) ^ 2) = (n : ℝ) := by
  rw [← Finset.sum_add_distrib]
  simp [Real.cos_sq_add_sin_sq]

/-- **Trace-norm (nuclear norm) bound for the cosine kernel.**

For all real phases `f, g : Fin n → ℝ`, the matrix `C i j = cos (f i - g j)` has bilinear form
bounded by `n ‖u‖ ‖v‖`; equivalently, the operator norm of `C` is at most `n`.  The proof
splits `C` into the two rank-one pieces coming from `cos (a - b) = cos a cos b + sin a sin b`
and bounds the sum of their nuclear norms, `‖cos f‖‖cos g‖ + ‖sin f‖‖sin g‖`, by `n`. -/
