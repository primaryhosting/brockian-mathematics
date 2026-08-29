/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
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

open Matrix

/-- The "cosine kernel" matrix attached to a family of angles `x : Fin n → ℝ`:
its `(i, j)` entry is `cos (x i - x j)`. -/
noncomputable def cosGram {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (x i - x j)

/-- The `n × 2` matrix whose rows are the unit vectors `(cos (x i), sin (x i))`. -/
noncomputable def cosSinRows {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin 2) ℝ :=
  Matrix.of fun i k => ![Real.cos (x i), Real.sin (x i)] k

/-- The cosine kernel matrix is the Gram matrix of the unit vectors
`(cos (x i), sin (x i))`. -/
theorem cosGram_eq_gram {n : ℕ} (x : Fin n → ℝ) :
    cosGram x = cosSinRows x * (cosSinRows x)ᴴ := by
  ext i j
  simp [cosGram, cosSinRows, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub]
  ring

/-- The cosine kernel matrix is positive semidefinite. -/
theorem cosGram_posSemidef {n : ℕ} (x : Fin n → ℝ) : (cosGram x).PosSemidef := by
  rw [cosGram_eq_gram]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The cosine kernel matrix is Hermitian (i.e. symmetric, over `ℝ`). -/
theorem cosGram_isHermitian {n : ℕ} (x : Fin n → ℝ) : (cosGram x).IsHermitian :=
  (cosGram_posSemidef x).isHermitian

/-- The trace of the cosine kernel matrix is `n`. -/
theorem cosGram_trace {n : ℕ} (x : Fin n → ℝ) : (cosGram x).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 1279.**  For every family of angles `x : Fin n → ℝ`, the trace norm
(the sum of the absolute values of the eigenvalues, equivalently the sum of the singular
values) of the cosine kernel matrix `(cos (x i - x j))ᵢⱼ` equals `n`.  This is sharp: the
matrix is positive semidefinite with trace `n`, and it has rank at most `2`. -/
theorem CosTraceNorm1279 {n : ℕ} (x : Fin n → ℝ) (h : (cosGram x).IsHermitian) :
    ∑ i, |h.eigenvalues i| = (n : ℝ) := by
  have hpsd : (cosGram x).PosSemidef := cosGram_posSemidef x
  have habs : ∀ i, |h.eigenvalues i| = h.eigenvalues i := by
    intro i
    exact abs_of_nonneg (hpsd.eigenvalues_nonneg i)
  calc ∑ i, |h.eigenvalues i| = ∑ i, h.eigenvalues i := by
        exact Finset.sum_congr rfl fun i _ => habs i
    _ = (cosGram x).trace := (h.trace_eq_sum_eigenvalues).symm
    _ = (n : ℝ) := cosGram_trace x

end Brockian

