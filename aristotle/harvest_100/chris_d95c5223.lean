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
open scoped Matrix

namespace Brockian

/-- The cosine Gram matrix of a family of angles `x : Fin n → ℝ`:
its `(i, j)` entry is `cos (x i - x j)`. -/
noncomputable def cosMatrix {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (x i - x j)

/-- The `2 × n` matrix whose columns are the unit vectors `(cos (x j), sin (x j))`. -/
noncomputable def cosSinRows {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k j => if k = 0 then Real.cos (x j) else Real.sin (x j)

lemma cosMatrix_eq_gram {n : ℕ} (x : Fin n → ℝ) :
    cosMatrix x = (cosSinRows x)ᴴ * cosSinRows x := by
  ext i j
  simp [cosMatrix, cosSinRows, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub]

lemma cosMatrix_posSemidef {n : ℕ} (x : Fin n → ℝ) : (cosMatrix x).PosSemidef := by
  rw [cosMatrix_eq_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma cosMatrix_isHermitian {n : ℕ} (x : Fin n → ℝ) : (cosMatrix x).IsHermitian :=
  (cosMatrix_posSemidef x).isHermitian

lemma cosMatrix_trace {n : ℕ} (x : Fin n → ℝ) : (cosMatrix x).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosMatrix]

/-- The trace norm (Schatten 1-norm) of a Hermitian real matrix: the sum of the absolute
values of its eigenvalues. -/
noncomputable def traceNorm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- **Cos Trace Norm 1597.**  For any angles `x : Fin n → ℝ`, the cosine Gram matrix
`C i j = cos (x i - x j)` is positive semidefinite, and hence its trace norm (the sum of the
absolute values of its eigenvalues) equals its trace, namely `n`. -/
theorem CosTraceNorm1597 {n : ℕ} (x : Fin n → ℝ) :
    traceNorm (cosMatrix_isHermitian x) = n := by
  have hpos : ∀ i, 0 ≤ (cosMatrix_isHermitian x).eigenvalues i := fun i =>
    (cosMatrix_posSemidef x).eigenvalues_nonneg i
  have h1 : traceNorm (cosMatrix_isHermitian x)
      = ∑ i, (cosMatrix_isHermitian x).eigenvalues i := by
    refine Finset.sum_congr rfl fun i _ => abs_of_nonneg (hpos i)
  rw [h1]
  have h2 := (cosMatrix_isHermitian x).trace_eq_sum_eigenvalues
  rw [cosMatrix_trace] at h2
  exact h2.symm

/-- Each eigenvalue of the cosine Gram matrix lies in `[0, n]`. -/
theorem cosMatrix_eigenvalue_le {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ (cosMatrix_isHermitian x).eigenvalues i ∧
      (cosMatrix_isHermitian x).eigenvalues i ≤ n := by
  have hpos : ∀ j, 0 ≤ (cosMatrix_isHermitian x).eigenvalues j := fun j =>
    (cosMatrix_posSemidef x).eigenvalues_nonneg j
  refine ⟨hpos i, ?_⟩
  have hsum : ∑ j, (cosMatrix_isHermitian x).eigenvalues j = n := by
    have h1 : traceNorm (cosMatrix_isHermitian x)
        = ∑ j, (cosMatrix_isHermitian x).eigenvalues j :=
      Finset.sum_congr rfl fun j _ => abs_of_nonneg (hpos j)
    rw [← h1]; exact CosTraceNorm1597 x
  calc (cosMatrix_isHermitian x).eigenvalues i
      ≤ ∑ j, (cosMatrix_isHermitian x).eigenvalues j :=
        Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ i)
    _ = n := hsum

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

