import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
Key Mathlib ingredients used below:
* `Matrix.IsHermitian.trace_eq_sum_eigenvalues` — the trace of a Hermitian matrix is the sum
  of its eigenvalues;
* `Matrix.posSemidef_conjTranspose_mul_self` — Gram matrices `Bᴴ * B` are positive semidefinite;
* `Matrix.PosSemidef.eigenvalues_nonneg` — eigenvalues of a PSD matrix are nonnegative.
-/

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (nuclear norm, Schatten 1-norm) of a Hermitian real matrix:
the sum of the absolute values of its eigenvalues. -/

theorem cosKernelAmp_one (x : n → ℝ) : cosKernelAmp (fun _ => (1 : ℝ)) x = cosKernel x := by
  ext i j
  simp [cosKernelAmp, cosKernel]

omit [Fintype n] [DecidableEq n] in
/-- The weighted cosine kernel is the Gram matrix of the planar vectors
`a i • (cos (x i), sin (x i))`. -/
