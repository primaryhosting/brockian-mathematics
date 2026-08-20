import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped Classical

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute values of
its eigenvalues. -/

theorem norm_trace_le_specTraceNorm {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ‖A.trace‖ ≤ specTraceNorm hA := by
  rw [hA.trace_eq_sum_eigenvalues]
  calc ‖∑ i, ((hA.eigenvalues i : ℝ) : ℂ)‖ ≤ ∑ i, ‖((hA.eigenvalues i : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
    _ = specTraceNorm hA := by
        simp [specTraceNorm, Complex.norm_real, Real.norm_eq_abs]

/-- The cosine trace is bounded in absolute value by the dimension. -/
