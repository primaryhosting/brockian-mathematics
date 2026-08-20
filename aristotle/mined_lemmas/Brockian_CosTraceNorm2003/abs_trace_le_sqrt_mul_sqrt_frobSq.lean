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

lemma abs_trace_le_sqrt_mul_sqrt_frobSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.trace| ≤ Real.sqrt n * Real.sqrt (frobSq A) := by
  have hfrob : (0 : ℝ) ≤ frobSq A :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : (A.trace) ^ 2 ≤ (n : ℝ) * frobSq A := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun _ => (1 : ℝ)) (fun i => A i i)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    calc (A.trace) ^ 2 = (∑ i, A i i) ^ 2 := by rw [Matrix.trace]; simp [Matrix.diag]
      _ ≤ (n : ℝ) * ∑ i, (A i i) ^ 2 := h
      _ ≤ (n : ℝ) * frobSq A := by
          exact mul_le_mul_of_nonneg_left (sum_diag_sq_le_frobSq A) (Nat.cast_nonneg n)
  have h1 : |A.trace| = Real.sqrt ((A.trace) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
  rw [h1, ← Real.sqrt_mul (Nat.cast_nonneg n)]
  exact Real.sqrt_le_sqrt hcs

/-- The Frobenius norm of a rotation matrix is `√2`. -/
