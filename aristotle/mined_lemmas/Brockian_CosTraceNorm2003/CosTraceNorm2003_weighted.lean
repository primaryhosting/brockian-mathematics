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

set_option maxHeartbeats 1000000

namespace Brockian

/-- The set of admissible bounds for the nuclear (trace) norm of a real matrix `A`:
`c` belongs to it iff `A` can be written as a finite sum of rank-one matrices
`u i ⊗ v i` whose total "product of Euclidean norms" is at most `c`. -/

theorem CosTraceNorm2003_weighted (n m : ℕ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    nuclearNorm (Matrix.of fun (j : Fin n) (k : Fin m) => a j * b k * Real.cos (x j - y k)) ≤
      Real.sqrt (∑ j, (a j) ^ 2) * Real.sqrt (∑ k, (b k) ^ 2) := by
  set p : ℝ := Real.sqrt (∑ j, (a j * Real.cos (x j)) ^ 2) with hp
  set q : ℝ := Real.sqrt (∑ j, (a j * Real.sin (x j)) ^ 2) with hq
  set s : ℝ := Real.sqrt (∑ k, (b k * Real.cos (y k)) ^ 2) with hs
  set t : ℝ := Real.sqrt (∑ k, (b k * Real.sin (y k)) ^ 2) with ht
  have key : p * s + q * t ≤ Real.sqrt (∑ j, (a j) ^ 2) * Real.sqrt (∑ k, (b k) ^ 2) := by
    have hpq : p ^ 2 + q ^ 2 = ∑ j, (a j) ^ 2 := by
      rw [hp, hq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := Real.sin_sq_add_cos_sq (x j)
      nlinarith [this]
    have hst : s ^ 2 + t ^ 2 = ∑ k, (b k) ^ 2 := by
      rw [hs, ht, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := Real.sin_sq_add_cos_sq (y k)
      nlinarith [this]
    have h := cs_two p q s t (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
    rw [hpq, hst] at h
    rwa [Real.sqrt_mul (by positivity)] at h
  refine nuclearNorm_le _
    ⟨2, ![fun j => a j * Real.cos (x j), fun j => a j * Real.sin (x j)],
      ![fun k => b k * Real.cos (y k), fun k => b k * Real.sin (y k)], ?_, ?_⟩
  · intro j k
    simp only [Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.cos_sub]
    ring
  · simpa [Fin.sum_univ_two, hp, hq, hs, ht] using key

/-- Trace-norm bound for the "sum" cosine kernel `A j k = cos (x j + y k)`. -/
