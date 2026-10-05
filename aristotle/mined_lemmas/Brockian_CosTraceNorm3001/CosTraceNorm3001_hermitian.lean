import Mathlib
/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset Matrix

/-- The trace norm (Schatten 1-norm) of a real symmetric matrix: the sum of the absolute
values of its eigenvalues, which for a symmetric matrix coincides with the sum of its
singular values. -/

theorem CosTraceNorm3001_hermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (θ : Fin n → ℝ) (hev : ∀ i, hA.eigenvalues i = Real.cos (θ i)) :
    |A.trace| ≤ hermitianTraceNorm hA ∧ hermitianTraceNorm hA ≤ (n : ℝ) := by
  constructor
  · rw [trace_eq_sum_eigenvalues hA]
    exact Finset.abs_sum_le_sum_abs _ _
  · calc hermitianTraceNorm hA ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by
          rw [hev i]; exact Real.abs_cos_le_one (θ i)
    _ = (n : ℝ) := by simp

end Brockian

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

