/-
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

/-- The trace norm (Schatten 1-norm) of a real Hermitian (i.e. symmetric) matrix:
the sum of the absolute values of its eigenvalues. -/
noncomputable def hermTraceNorm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- The cosine Gram matrix of a family of angles: `(i, j) ↦ cos (θ i - θ j)`. -/
noncomputable def cosGram (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The two-row matrix whose columns are the unit vectors `(cos θ j, sin θ j)`. -/
noncomputable def cosSinRows (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k j => if k = 0 then Real.cos (θ j) else Real.sin (θ j)

/-- Key factorization: the cosine Gram matrix is `Bᴴ * B` for the two-row matrix `B`
of unit vectors, by the cosine subtraction formula. -/
lemma cosGram_eq_conjTranspose_mul_self (n : ℕ) (θ : Fin n → ℝ) :
    cosGram n θ = Matrix.conjTranspose (cosSinRows n θ) * cosSinRows n θ := by
  ext i j
  simp [cosGram, cosSinRows, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub, mul_comm]

/-- Key intermediate lemma: the cosine Gram matrix is positive semidefinite. -/
lemma cosGram_posSemidef (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).PosSemidef := by
  rw [cosGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The diagonal entries of the cosine Gram matrix are `1`, hence its trace is `n`. -/
lemma cosGram_trace (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).trace = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 1279.**  The trace norm of the `n × n` cosine Gram matrix
`(i, j) ↦ cos (θ i - θ j)` equals `n`, for any family of angles `θ`. -/
theorem CosTraceNorm1279 (n : ℕ) (θ : Fin n → ℝ) :
    hermTraceNorm (cosGram_posSemidef n θ).isHermitian = (n : ℝ) := by
  have hpsd := cosGram_posSemidef n θ
  have habs : ∀ i, |hpsd.isHermitian.eigenvalues i| = hpsd.isHermitian.eigenvalues i :=
    fun i => abs_of_nonneg (hpsd.eigenvalues_nonneg i)
  have htr : (cosGram n θ).trace = ∑ i, (hpsd.isHermitian.eigenvalues i : ℝ) :=
    hpsd.isHermitian.trace_eq_sum_eigenvalues
  calc hermTraceNorm hpsd.isHermitian
      = ∑ i, hpsd.isHermitian.eigenvalues i := by
        simp [hermTraceNorm, habs]
    _ = (cosGram n θ).trace := htr.symm
    _ = (n : ℝ) := cosGram_trace n θ

end Brockian

