import Mathlib

/-!
# Trace-norm bounds for cosine Gram matrices (the `CosTraceNorm` family)

For a real symmetric matrix `A` we define its *trace norm* (nuclear norm, Schatten
`1`-norm) as the sum of the absolute values of its eigenvalues.

The main objects of study are the *cosine Gram matrices*
`cosMatrix f θ = (cos (f * (θ i - θ j)))_{i,j}` and their linear combinations
`cosCombo c f θ = ∑ k, c k • cosMatrix (f k) θ`.

The main result `Brockian.CosTraceNorm1279` gives two-sided trace-norm bounds for
`cosCombo c f θ` with arbitrary (possibly signed) coefficients `c`.
-/

namespace Brockian

open Matrix Finset

section TraceNorm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- The trace norm (nuclear norm, Schatten `1`-norm) of a real symmetric matrix:
the sum of the absolute values of its eigenvalues. -/
noncomputable def traceNorm (hA : A.IsHermitian) : ℝ := ∑ i, |hA.eigenvalues i|

lemma traceNorm_nonneg (hA : A.IsHermitian) : 0 ≤ traceNorm hA :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma trace_le_traceNorm (hA : A.IsHermitian) : A.trace ≤ traceNorm hA := by
  rw [hA.trace_eq_sum_eigenvalues]
  exact Finset.sum_le_sum fun i _ => le_abs_self _

lemma abs_trace_le_traceNorm (hA : A.IsHermitian) : |A.trace| ≤ traceNorm hA := by
  rw [hA.trace_eq_sum_eigenvalues]
  exact Finset.abs_sum_le_sum_abs _ _

lemma traceNorm_eq_trace_of_posSemidef (hA : A.PosSemidef) :
    traceNorm hA.isHermitian = A.trace := by
  rw [hA.isHermitian.trace_eq_sum_eigenvalues]
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hA.eigenvalues_nonneg i)

/-- The quadratic forms of a matrix `P` along an orthonormal eigenbasis of a symmetric
matrix `A` sum to the trace of `P`. -/
lemma sum_eigenbasis_quadraticForm (hA : A.IsHermitian) (P : Matrix ι ι ℝ) :
    ∑ i, (star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ
      (P *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ))) = P.trace := by
  set U : Matrix ι ι ℝ := (hA.eigenvectorUnitary : Matrix ι ι ℝ) with hU
  have key : ∀ i, (star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ
      (P *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ))) = (star U * P * U) i i := by
    intro i
    simp only [Matrix.mul_apply, dotProduct, mulVec, Matrix.star_apply, hU, Finset.mul_sum,
      Finset.sum_mul, mul_assoc, Matrix.IsHermitian.eigenvectorUnitary_apply, star_trivial]
    rw [Finset.sum_comm]
  simp_rw [key]
  have h1 : ∑ i, (star U * P * U) i i = (star U * P * U).trace := rfl
  have h2 : U * star U = 1 := by simp [hU]
  rw [h1, Matrix.trace_mul_cycle, h2, Matrix.one_mul]

/-- If a symmetric matrix is a difference of two positive semidefinite matrices, then its
trace norm is bounded by the sum of their traces. -/
lemma traceNorm_le_of_sub_posSemidef {P N : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hP : P.PosSemidef) (hN : N.PosSemidef) (hPN : A = P - N) :
    traceNorm hA ≤ P.trace + N.trace := by
  subst hPN
  have hev : ∀ i, hA.eigenvalues i =
      (star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ (P *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ)))
      - (star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ
          (N *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ))) := by
    intro i
    rw [hA.eigenvalues_eq i]
    simp [Matrix.sub_mulVec, dotProduct_sub]
  calc traceNorm hA
      ≤ ∑ i, ((star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ
            (P *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ)))
          + (star (⇑(hA.eigenvectorBasis i) : ι → ℝ) ⬝ᵥ
            (N *ᵥ (⇑(hA.eigenvectorBasis i) : ι → ℝ)))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hev i]
        exact abs_sub_le_iff.mpr
          ⟨by linarith [hN.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis i) : ι → ℝ)],
           by linarith [hP.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis i) : ι → ℝ)]⟩
    _ = P.trace + N.trace := by
        rw [Finset.sum_add_distrib, sum_eigenbasis_quadraticForm hA P,
          sum_eigenbasis_quadraticForm hA N]

end TraceNorm

section Cos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cosine Gram matrix of the phases `θ` at frequency `f`. -/
noncomputable def cosMatrix (f : ℝ) (θ : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => Real.cos (f * (θ i - θ j))

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma cosMatrix_apply (f : ℝ) (θ : ι → ℝ) (i j : ι) :
    cosMatrix f θ i j = Real.cos (f * (θ i - θ j)) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma cosMatrix_isHermitian (f : ℝ) (θ : ι → ℝ) : (cosMatrix f θ).IsHermitian := by
  ext i j
  show Real.cos (f * (θ j - θ i)) = Real.cos (f * (θ i - θ j))
  rw [← Real.cos_neg (f * (θ i - θ j))]
  ring_nf

omit [DecidableEq ι] in
/-- The quadratic form of a cosine Gram matrix is a sum of two squares. -/
lemma cosMatrix_quadraticForm (f : ℝ) (θ : ι → ℝ) (x : ι → ℝ) :
    star x ⬝ᵥ (cosMatrix f θ *ᵥ x)
      = (∑ i, x i * Real.cos (f * θ i)) ^ 2 + (∑ i, x i * Real.sin (f * θ i)) ^ 2 := by
  simp only [dotProduct, mulVec, cosMatrix, Matrix.of_apply, star_trivial, sq,
    Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_sub, Real.cos_sub]
  ring

omit [DecidableEq ι] in
lemma cosMatrix_posSemidef (f : ℝ) (θ : ι → ℝ) : (cosMatrix f θ).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (cosMatrix_isHermitian f θ) fun x => by
    rw [cosMatrix_quadraticForm]
    positivity

omit [DecidableEq ι] in
@[simp] lemma cosMatrix_trace (f : ℝ) (θ : ι → ℝ) :
    (cosMatrix f θ).trace = (Fintype.card ι : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosMatrix]

/-- A linear combination of cosine Gram matrices at frequencies `f k` with coefficients `c k`. -/
noncomputable def cosCombo {m : ℕ} (c f : Fin m → ℝ) (θ : ι → ℝ) : Matrix ι ι ℝ :=
  ∑ k, c k • cosMatrix (f k) θ

omit [Fintype ι] [DecidableEq ι] in
lemma cosCombo_isHermitian {m : ℕ} (c f : Fin m → ℝ) (θ : ι → ℝ) :
    (cosCombo c f θ).IsHermitian :=
  isSelfAdjoint_sum _ fun k _ =>
    IsSelfAdjoint.smul (star_trivial (c k)) (cosMatrix_isHermitian (f k) θ)

omit [DecidableEq ι] in
@[simp] lemma cosCombo_trace {m : ℕ} (c f : Fin m → ℝ) (θ : ι → ℝ) :
    (cosCombo c f θ).trace = (Fintype.card ι : ℝ) * ∑ k, c k := by
  simp [cosCombo, Matrix.trace_sum, Finset.sum_mul, mul_comm]

omit [DecidableEq ι] in
lemma cosCombo_posSemidef {m : ℕ} {c : Fin m → ℝ} (f : Fin m → ℝ) (θ : ι → ℝ)
    (hc : ∀ k, 0 ≤ c k) : (cosCombo c f θ).PosSemidef :=
  Matrix.posSemidef_sum _ fun k _ => (cosMatrix_posSemidef (f k) θ).smul (hc k)

/-- For nonnegative coefficients the trace norm of `cosCombo c f θ` is exactly
`(card ι) * ∑ k, c k`. -/
theorem traceNorm_cosCombo_of_nonneg {m : ℕ} {c : Fin m → ℝ} (f : Fin m → ℝ) (θ : ι → ℝ)
    (hc : ∀ k, 0 ≤ c k) :
    traceNorm (cosCombo_isHermitian c f θ) = (Fintype.card ι : ℝ) * ∑ k, c k := by
  rw [← cosCombo_trace c f θ]
  exact traceNorm_eq_trace_of_posSemidef (cosCombo_posSemidef f θ hc)

/-- The trace norm of a single cosine Gram matrix is the cardinality of the index set. -/
theorem traceNorm_cosMatrix (f : ℝ) (θ : ι → ℝ) :
    traceNorm (cosMatrix_isHermitian f θ) = (Fintype.card ι : ℝ) := by
  rw [← cosMatrix_trace f θ]
  exact traceNorm_eq_trace_of_posSemidef (cosMatrix_posSemidef f θ)

omit [Fintype ι] [DecidableEq ι] in
/-- The splitting of `cosCombo` into its positive and negative parts. -/
lemma cosCombo_eq_sub {m : ℕ} (c f : Fin m → ℝ) (θ : ι → ℝ) :
    cosCombo c f θ = cosCombo (fun k => max (c k) 0) f θ
      - cosCombo (fun k => max (-c k) 0) f θ := by
  simp only [cosCombo, ← Finset.sum_sub_distrib, ← sub_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rcases le_total 0 (c k) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
  · rw [max_eq_right h, max_eq_left (by linarith), zero_sub, neg_neg]

/-- **Trace-norm bounds for cosine Gram combinations.**
For arbitrary real coefficients `c` and frequencies `f`, the trace norm of
`cosCombo c f θ = ∑ k, c k • (cos (f k * (θ i - θ j)))_{i,j}` satisfies
`|card ι * ∑ k, c k| ≤ ‖cosCombo c f θ‖₁ ≤ card ι * ∑ k, |c k|`.
The two bounds coincide (so both are attained) when all `c k` have the same sign. -/
theorem CosTraceNorm1279 {m : ℕ} (c f : Fin m → ℝ) (θ : ι → ℝ) :
    |(Fintype.card ι : ℝ) * ∑ k, c k| ≤ traceNorm (cosCombo_isHermitian c f θ) ∧
      traceNorm (cosCombo_isHermitian c f θ) ≤ (Fintype.card ι : ℝ) * ∑ k, |c k| := by
  constructor
  · have := abs_trace_le_traceNorm (cosCombo_isHermitian c f θ)
    rwa [cosCombo_trace] at this
  · have hP := cosCombo_posSemidef (c := fun k => max (c k) 0) f θ fun k => le_max_right _ _
    have hN := cosCombo_posSemidef (c := fun k => max (-c k) 0) f θ fun k => le_max_right _ _
    have hbound := traceNorm_le_of_sub_posSemidef (cosCombo_isHermitian c f θ) hP hN
      (cosCombo_eq_sub c f θ)
    rw [cosCombo_trace, cosCombo_trace, ← mul_add, ← Finset.sum_add_distrib] at hbound
    refine hbound.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases le_total 0 (c k) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), add_zero, abs_of_nonneg h]
    · rw [max_eq_right h, max_eq_left (by linarith), zero_add, abs_of_nonpos h]

end Cos

end Brockian

section Verification

#print axioms Brockian.CosTraceNorm1279
#print axioms Brockian.traceNorm_cosCombo_of_nonneg
#print axioms Brockian.traceNorm_cosMatrix

end Verification

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

