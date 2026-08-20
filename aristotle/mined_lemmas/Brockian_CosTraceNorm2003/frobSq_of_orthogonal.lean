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

lemma frobSq_of_orthogonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A * A.transpose = 1) : frobSq A = n := by
  have h1 : (A * A.transpose).trace = ((1 : Matrix (Fin n) (Fin n) ℝ)).trace := by rw [h]
  rw [Matrix.trace_one, Fintype.card_fin] at h1
  calc frobSq A = ∑ i, ∑ j, A i j * (A.transpose) j i := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.transpose_apply]; ring
    _ = (A * A.transpose).trace := by
        rw [Matrix.trace]
        exact (Finset.sum_congr rfl fun i _ => by
          simp [Matrix.diag, Matrix.mul_apply]).symm
    _ = (n : ℝ) := h1

/-- **New trace-norm bound.** The trace of a real orthogonal `n × n` matrix is
bounded in absolute value by `n`. -/
