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

theorem abs_trace_le_hermTraceNorm {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    |A.trace| ≤ hermTraceNorm hA := by
  rw [hA.trace_eq_sum_eigenvalues, hermTraceNorm]
  exact Finset.abs_sum_le_sum_abs _ _

/-- For a positive semidefinite matrix the trace norm is just the trace. -/
