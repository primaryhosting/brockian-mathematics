/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Real Matrix

namespace Brockian

/-- The entrywise cosine of a real matrix has trace equal to the sum of the cosines of the
diagonal entries. -/
lemma trace_map_cos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.map Real.cos).trace = ∑ i, Real.cos (A i i) := by
  simp [Matrix.trace, Matrix.diag]

/-- Each summand of the cosine trace is bounded by `1`. -/
lemma one_sub_cos_nonneg (x : ℝ) : 0 ≤ 1 - Real.cos x := by
  have := Real.cos_le_one x
  linarith

/-- **Cosine trace norm bound.**

For every real `n × n` matrix `A`, the trace of the entrywise cosine `A.map cos` has absolute
value at most `n`, and it attains the value `n` exactly when every diagonal entry of `A` is an
integer multiple of `2π`. -/
theorem CosTraceNorm3499 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |(A.map Real.cos).trace| ≤ (n : ℝ) ∧
      ((A.map Real.cos).trace = (n : ℝ) ↔ ∀ i, ∃ k : ℤ, A i i = 2 * π * k) := by
  have htr : (A.map Real.cos).trace = ∑ i, Real.cos (A i i) := trace_map_cos A
  constructor
  · rw [htr]
    calc |∑ i, Real.cos (A i i)| ≤ ∑ i : Fin n, |Real.cos (A i i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact Real.abs_cos_le_one _
      _ = (n : ℝ) := by simp
  · rw [htr]
    constructor
    · intro hsum i
      have hzero : ∑ i : Fin n, (1 - Real.cos (A i i)) = 0 := by
        rw [Finset.sum_sub_distrib]
        simp [hsum]
      have hall : ∀ j ∈ Finset.univ, 1 - Real.cos (A j j) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => one_sub_cos_nonneg (A j j))).1 hzero
      have hi : Real.cos (A i i) = 1 := by
        have := hall i (Finset.mem_univ i)
        linarith
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (A i i)).1 hi
      exact ⟨k, by rw [← hk]; ring⟩
    · intro h
      have : ∀ i : Fin n, Real.cos (A i i) = 1 := by
        intro i
        obtain ⟨k, hk⟩ := h i
        rw [hk]
        exact (Real.cos_eq_one_iff _).2 ⟨k, by ring⟩
      simp [this]

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

