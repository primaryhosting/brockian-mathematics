/-
/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

namespace Brockian

open Finset

/-- The trace of a diagonal matrix of cosines is the sum of those cosines. -/
lemma trace_cos_diagonal {n : ℕ} (θ : Fin n → ℝ) :
    (Matrix.diagonal fun i => Real.cos (θ i)).trace = ∑ i, Real.cos (θ i) := by
  simp [Matrix.trace_diagonal]

/-- Each cosine sum is bounded in absolute value by the number of terms. -/
lemma abs_sum_cos_le {n : ℕ} (θ : Fin n → ℝ) :
    |∑ i, Real.cos (θ i)| ≤ (n : ℝ) := by
  have h : |∑ i, Real.cos (θ i)| ≤ ∑ _i : Fin n, (1 : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    exact abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  simpa using h

/-- Quadratic (second-order) lower bound for the cosine sum. -/
lemma sum_cos_ge_quadratic {n : ℕ} (θ : Fin n → ℝ) :
    (n : ℝ) - (∑ i, (θ i) ^ 2) / 2 ≤ ∑ i, Real.cos (θ i) := by
  have h : ∑ i, (1 - (θ i) ^ 2 / 2) ≤ ∑ i, Real.cos (θ i) :=
    Finset.sum_le_sum fun i _ => Real.one_sub_sq_div_two_le_cos
  have h2 : ∑ i, (1 - (θ i) ^ 2 / 2) = (n : ℝ) - (∑ i, (θ i) ^ 2) / 2 := by
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_div]
  rw [← h2]
  exact h

/--
**Cos Trace Norm 3001.**

For the diagonal matrix `M` whose entries are `cos (θ i)`:

* its trace is bounded in absolute value by the dimension `n`;
* the trace deviates from `n` by at most `(∑ θ i ^ 2) / 2`
  (a second-order trace-norm bound);
* the sum of the absolute values of its diagonal entries (its trace norm,
  since `M` is diagonal) is at most `n`.
-/
theorem CosTraceNorm3001 {n : ℕ} (θ : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M = Matrix.diagonal fun i => Real.cos (θ i)) :
    |M.trace| ≤ (n : ℝ) ∧
      |M.trace - (n : ℝ)| ≤ (∑ i, (θ i) ^ 2) / 2 ∧
      ∑ i, |M i i| ≤ (n : ℝ) := by
  subst hM
  have htr : (Matrix.diagonal fun i => Real.cos (θ i)).trace = ∑ i, Real.cos (θ i) :=
    trace_cos_diagonal θ
  refine ⟨by rw [htr]; exact abs_sum_cos_le θ, ?_, ?_⟩
  · rw [htr, abs_le]
    constructor
    · have := sum_cos_ge_quadratic θ
      linarith
    · have h : ∑ i, Real.cos (θ i) ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.cos_le_one _
      have hq : (0 : ℝ) ≤ ∑ i, (θ i) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one] at h
      linarith
  · have h : ∑ i, |(Matrix.diagonal fun i => Real.cos (θ i)) i i| ≤ ∑ _i : Fin n, (1 : ℝ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [Matrix.diagonal_apply_eq]
      exact abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    simpa using h

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

