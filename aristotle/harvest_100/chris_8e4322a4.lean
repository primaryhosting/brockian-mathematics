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

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian real matrix, defined as the sum of the
absolute values of its eigenvalues (and `0` on non-Hermitian matrices). -/
noncomputable def traceNorm (A : Matrix n n ℝ) : ℝ := by
  classical
  exact if h : A.IsHermitian then ∑ i, |h.eigenvalues i| else 0

/-- The weighted cosine Gram matrix: `C i j = w i * w j * cos (θ i - θ j)`. -/
noncomputable def cosGram (w θ : n → ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => w i * w j * Real.cos (θ i - θ j)

/-- The rank-≤2 factor of the weighted cosine Gram matrix. -/
noncomputable def cosFactor (w θ : n → ℝ) : Matrix n (Fin 2) ℝ :=
  Matrix.of fun i k => if k = 0 then w i * Real.cos (θ i) else w i * Real.sin (θ i)

omit [Fintype n] [DecidableEq n] in
theorem cosGram_eq_factor_mul (w θ : n → ℝ) :
    cosGram w θ = cosFactor w θ * (cosFactor w θ).conjTranspose := by
  ext i j
  simp only [cosGram, cosFactor, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_trivial]
  rw [Fin.sum_univ_two]
  simp only [Real.cos_sub]
  norm_num
  ring

omit [DecidableEq n] in
/-- The weighted cosine Gram matrix is positive semidefinite. -/
theorem cosGram_posSemidef (w θ : n → ℝ) : (cosGram w θ).PosSemidef := by
  rw [cosGram_eq_factor_mul]
  exact Matrix.posSemidef_self_mul_conjTranspose _

omit [DecidableEq n] in
theorem trace_cosGram (w θ : n → ℝ) : (cosGram w θ).trace = ∑ i, (w i) ^ 2 := by
  simp [Matrix.trace, Matrix.diag, cosGram, sq]

/-- **Cos Trace Norm 2003.**  For any weights `w` and phases `θ`, the trace norm of the weighted
cosine Gram matrix `C i j = w i * w j * cos (θ i - θ j)` is exactly `∑ i, (w i)^2`. -/
theorem CosTraceNorm2003 (w θ : n → ℝ) : traceNorm (cosGram w θ) = ∑ i, (w i) ^ 2 := by
  classical
  have hpsd := cosGram_posSemidef w θ
  have hherm := hpsd.isHermitian
  rw [traceNorm, dif_pos hherm]
  have habs : ∀ i, |hherm.eigenvalues i| = hherm.eigenvalues i := fun i =>
    abs_of_nonneg (hpsd.eigenvalues_nonneg i)
  simp only [habs]
  have htr : (cosGram w θ).trace = ∑ i, (hherm.eigenvalues i : ℝ) :=
    hherm.trace_eq_sum_eigenvalues
  rw [← htr, trace_cosGram]

/-- Unweighted corollary: the trace norm of the cosine matrix `cos (θ i - θ j)` is the
dimension of the space. -/
theorem CosTraceNorm2003_unit (θ : n → ℝ) :
    traceNorm (cosGram (fun _ => (1 : ℝ)) θ) = (Fintype.card n : ℝ) := by
  rw [CosTraceNorm2003]
  simp [Finset.card_univ]

/-- Consequently the trace norm of any such cosine Gram matrix is bounded by
`(Fintype.card n) * (sup of the squared weights)`. -/
theorem CosTraceNorm2003_bound (w θ : n → ℝ) (M : ℝ) (hM : ∀ i, |w i| ≤ M) :
    traceNorm (cosGram w θ) ≤ (Fintype.card n : ℝ) * M ^ 2 := by
  rw [CosTraceNorm2003]
  calc ∑ i, (w i) ^ 2 ≤ ∑ _i : n, M ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hM i) 2
    _ = (Fintype.card n : ℝ) * M ^ 2 := by
        simp [Finset.card_univ]

end Brockian

