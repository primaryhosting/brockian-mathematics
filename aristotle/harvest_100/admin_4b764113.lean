/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
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

/-- The quadratic form of the cosine kernel `cos (θ i - θ j)` is a sum of two squares. -/
theorem cos_kernel_quadratic_form {ι : Type*} [Fintype ι] (θ x : ι → ℝ) :
    ∑ i, ∑ j, x i * x j * Real.cos (θ i - θ j)
      = (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2 := by
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.cos_sub]
  ring

/-- The cosine kernel matrix `A i j = cos (θ i - θ j)` is positive semidefinite as a real
quadratic form. -/
theorem cos_kernel_nonneg {ι : Type*} [Fintype ι] (θ x : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * Real.cos (θ i - θ j) := by
  rw [cos_kernel_quadratic_form]
  positivity

/-- Trace-norm style upper bound: the cosine kernel form is bounded by
`(card ι) * ‖x‖²`, the trace of the kernel matrix times the squared norm. -/
theorem cos_kernel_le_card_mul {ι : Type*} [Fintype ι] (θ x : ι → ℝ) :
    ∑ i, ∑ j, x i * x j * Real.cos (θ i - θ j)
      ≤ (Fintype.card ι : ℝ) * ∑ i, x i ^ 2 := by
  rw [cos_kernel_quadratic_form]
  have hc : (∑ i, x i * Real.cos (θ i)) ^ 2
      ≤ (∑ i, x i ^ 2) * ∑ i, Real.cos (θ i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hs : (∑ i, x i * Real.sin (θ i)) ^ 2
      ≤ (∑ i, x i ^ 2) * ∑ i, Real.sin (θ i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsum : (∑ i, Real.cos (θ i) ^ 2) + ∑ i, Real.sin (θ i) ^ 2
      = (Fintype.card ι : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp [Real.cos_sq_add_sin_sq, Finset.card_univ]
  calc (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2
      ≤ (∑ i, x i ^ 2) * (∑ i, Real.cos (θ i) ^ 2)
        + (∑ i, x i ^ 2) * ∑ i, Real.sin (θ i) ^ 2 := add_le_add hc hs
    _ = (∑ i, x i ^ 2) * ((∑ i, Real.cos (θ i) ^ 2) + ∑ i, Real.sin (θ i) ^ 2) := by ring
    _ = (Fintype.card ι : ℝ) * ∑ i, x i ^ 2 := by rw [hsum]; ring

/-- The cosine kernel matrix is positive semidefinite in the sense of `Matrix.PosSemidef`. -/
theorem cos_kernel_posSemidef {ι : Type*} [Fintype ι] (θ : ι → ℝ) :
    (Matrix.of (fun i j : ι => Real.cos (θ i - θ j))).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose, ← Real.cos_neg (θ i - θ j)]
  · intro x
    refine le_of_le_of_eq (cos_kernel_nonneg θ x) ?_
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_comm]

/-- The trace norm (sum of the absolute values of the eigenvalues, equivalently the sum of the
singular values) of the cosine kernel matrix equals `card ι`. -/
theorem cos_kernel_sum_abs_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ι → ℝ)
    (hA : (Matrix.of (fun i j : ι => Real.cos (θ i - θ j))).IsHermitian) :
    ∑ i, |hA.eigenvalues i| = (Fintype.card ι : ℝ) := by
  have hpos := cos_kernel_posSemidef θ
  have habs : ∀ i, |hA.eigenvalues i| = hA.eigenvalues i := fun i =>
    abs_of_nonneg (hpos.eigenvalues_nonneg i)
  have htr : (Matrix.of (fun i j : ι => Real.cos (θ i - θ j))).trace
      = ∑ i, (hA.eigenvalues i : ℝ) := hA.trace_eq_sum_eigenvalues
  simp only [habs]
  rw [← htr]
  simp [Matrix.trace, Matrix.diag, Finset.card_univ]

/-- Sharpness of the upper bound: for constant phases and the all-ones vector, the
cosine kernel form equals `(card ι) * ‖x‖²`. -/
theorem cos_kernel_bound_sharp {ι : Type*} [Fintype ι] :
    ∑ i : ι, ∑ _j : ι, (1 : ℝ) * 1 * Real.cos ((0 : ι → ℝ) i - (0 : ι → ℝ) i)
      = (Fintype.card ι : ℝ) * ∑ _i : ι, (1 : ℝ) ^ 2 := by
  simp [Finset.card_univ]

/-- **Cos Trace Norm 2707.**
For any finite index type `ι` and any phases `θ : ι → ℝ`, the cosine kernel matrix
`A i j = cos (θ i - θ j)` is positive semidefinite, has trace `card ι`, and hence has trace
norm (sum of absolute values of its eigenvalues) exactly `card ι`; consequently its quadratic
form satisfies the two-sided bound `0 ≤ xᵀ A x ≤ (card ι) * ‖x‖²` for every real vector `x`. -/
theorem CosTraceNorm2707 {ι : Type*} [Fintype ι] [DecidableEq ι] (θ x : ι → ℝ) :
    (Matrix.of (fun i j : ι => Real.cos (θ i - θ j))).PosSemidef ∧
      (Matrix.of (fun i j : ι => Real.cos (θ i - θ j))).trace = (Fintype.card ι : ℝ) ∧
      (∑ i, |(cos_kernel_posSemidef θ).1.eigenvalues i| = (Fintype.card ι : ℝ)) ∧
      (0 ≤ ∑ i, ∑ j, x i * x j * Real.cos (θ i - θ j)) ∧
      ∑ i, ∑ j, x i * x j * Real.cos (θ i - θ j)
        ≤ (Fintype.card ι : ℝ) * ∑ i, x i ^ 2 :=
  ⟨cos_kernel_posSemidef θ,
    by simp [Matrix.trace, Matrix.diag, Finset.card_univ],
    cos_kernel_sum_abs_eigenvalues θ _,
    cos_kernel_nonneg θ x,
    cos_kernel_le_card_mul θ x⟩

end Brockian

