/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
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

section CosTraceNorm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute
values of its eigenvalues. -/

theorem hermTraceNorm_cosGram (x : n → ℝ) :
    hermTraceNorm (cosGram_isHermitian x) = (Fintype.card n : ℝ) := by
  have hpsd := cosGram_posSemidef x
  have habs : ∀ i, |(cosGram_isHermitian x).eigenvalues i|
      = (cosGram_isHermitian x).eigenvalues i := fun i =>
    abs_of_nonneg (hpsd.eigenvalues_nonneg i)
  have hsum : ∑ i, ((cosGram_isHermitian x).eigenvalues i : ℝ) = (cosGram x).trace :=
    ((cosGram_isHermitian x).trace_eq_sum_eigenvalues).symm
  calc hermTraceNorm (cosGram_isHermitian x)
      = ∑ i, (cosGram_isHermitian x).eigenvalues i := by
        simp only [hermTraceNorm, habs]
    _ = (cosGram x).trace := hsum
    _ = (Fintype.card n : ℝ) := trace_cosGram x

/-- Corollary: the trace norm of a cosine Gram matrix is bounded by the size of the
index set (with equality). -/
