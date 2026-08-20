/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The squared Frobenius (Hilbert–Schmidt) norm of a square real matrix:
the sum of the squares of all its entries. -/

theorem abs_trace_le_card_of_orthogonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A * A.transpose = 1) : |A.trace| ≤ n := by
  have hb := abs_trace_le_sqrt_mul_sqrt_frobSq A
  rw [frobSq_of_orthogonal A h] at hb
  rwa [Real.mul_self_sqrt (Nat.cast_nonneg n)] at hb

/-- The plane rotation is orthogonal. -/
