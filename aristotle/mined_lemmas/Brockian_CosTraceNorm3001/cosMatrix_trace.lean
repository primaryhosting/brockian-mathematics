/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not permit a
-- module docstring before `import`; the module docstring is repeated after the imports.)

import Mathlib

/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The `2 × n` real matrix whose `i`-th column is the unit vector
`(cos (θ i), sin (θ i))`. -/

lemma cosMatrix_trace {n : ℕ} (θ : Fin n → ℝ) : (cosMatrix θ).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosMatrix]

/--
**Cos Trace Norm 3001.**

For any phases `θ : Fin n → ℝ`, the trace norm (Schatten `1`-norm, i.e. the sum of the
absolute values of the eigenvalues of this symmetric matrix, which are its singular values)
of the cosine kernel matrix `M i j = cos (θ i - θ j)` equals `n`.

The matrix is positive semidefinite, being the Gram matrix of the unit vectors
`(cos (θ i), sin (θ i))`, so its trace norm coincides with its trace, which is `n`
since every diagonal entry is `cos 0 = 1`.

Key Mathlib ingredients: `Matrix.posSemidef_conjTranspose_mul_self`,
`Matrix.PosSemidef.eigenvalues_nonneg`, `Matrix.IsHermitian.trace_eq_sum_eigenvalues`.
-/
