/-
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The circular (cosine) Gram matrix of a family of angles `θ : Fin n → ℝ`:
its `(i, j)` entry is `cos (θ i - θ j)`. -/

theorem cosGram_traceNorm (n : ℕ) (θ : Fin n → ℝ) :
    ∑ i, |(cosGram_posSemidef n θ).isHermitian.eigenvalues i| = n := by
  have hpsd := cosGram_posSemidef n θ
  calc ∑ i, |hpsd.isHermitian.eigenvalues i|
      = ∑ i, hpsd.isHermitian.eigenvalues i :=
        Finset.sum_congr rfl fun i _ => abs_of_nonneg (hpsd.eigenvalues_nonneg i)
    _ = (cosGram n θ).trace := hpsd.isHermitian.trace_eq_sum_eigenvalues.symm
    _ = n := trace_cosGram n θ

/-- **Cos Trace Norm 1279.**
For any family of `1279` angles `θ`, the cosine Gram matrix `A i j = cos (θ i - θ j)` is
positive semidefinite, has trace `1279`, and its trace norm (the sum of the absolute values
of its eigenvalues, equivalently the sum of its singular values) is exactly `1279`. -/
