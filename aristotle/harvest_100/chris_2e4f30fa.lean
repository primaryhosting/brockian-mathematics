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
open scoped MatrixOrder

namespace Brockian

open Matrix

/-- The *cosine Gram matrix* of a family of phases `θ : Fin n → ℝ`:
its `(i, j)` entry is `cos (θ i - θ j)`. -/
noncomputable def cosGram {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The `2 × n` matrix whose columns are the unit vectors `(cos (θ j), sin (θ j))`. -/
noncomputable def phaseVectors {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k j => if k = 0 then Real.cos (θ j) else Real.sin (θ j)

/-- The trace norm (Schatten `1`-norm) of a square real matrix: the trace of `|A| = √(Aᴴ A)`,
equivalently the sum of the singular values of `A`. -/
noncomputable def traceNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (CFC.abs A).trace

/-- For a positive semidefinite matrix the trace norm coincides with the trace. -/
theorem traceNorm_of_posSemidef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    traceNorm A = A.trace := by
  rw [traceNorm, CFC.abs_of_nonneg A hA.nonneg]

/-- The cosine Gram matrix is the Gram matrix of the unit vectors `(cos θ j, sin θ j)`. -/
theorem cosGram_eq_conjTranspose_mul_self {n : ℕ} (θ : Fin n → ℝ) :
    cosGram θ = (phaseVectors θ)ᴴ * phaseVectors θ := by
  ext i j
  simp only [cosGram, phaseVectors, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_trivial]
  rw [Fin.sum_univ_two]
  simp [Real.cos_sub]

/-- The cosine Gram matrix is positive semidefinite. -/
theorem cosGram_posSemidef {n : ℕ} (θ : Fin n → ℝ) : (cosGram θ).PosSemidef := by
  rw [cosGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The cosine Gram matrix has trace `n`, since its diagonal entries are `cos 0 = 1`. -/
theorem cosGram_trace {n : ℕ} (θ : Fin n → ℝ) : (cosGram θ).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 2003.**  For any phases `θ : Fin n → ℝ`, the cosine Gram matrix
`C i j = cos (θ i - θ j)` is positive semidefinite, has trace `n`, and its trace norm
(the sum of its singular values) is exactly `n`. -/
theorem CosTraceNorm2003 {n : ℕ} (θ : Fin n → ℝ) :
    (cosGram θ).PosSemidef ∧ (cosGram θ).trace = (n : ℝ) ∧ traceNorm (cosGram θ) = (n : ℝ) :=
  ⟨cosGram_posSemidef θ, cosGram_trace θ,
    (traceNorm_of_posSemidef (cosGram_posSemidef θ)).trans (cosGram_trace θ)⟩

/-- The trace norm of the cosine Gram matrix is bounded by the size of the matrix. -/
theorem cosGram_traceNorm_le {n : ℕ} (θ : Fin n → ℝ) : traceNorm (cosGram θ) ≤ (n : ℝ) :=
  le_of_eq (CosTraceNorm2003 θ).2.2

/-- For an arbitrary matrix of cosines, the trace is bounded in absolute value by `n`. -/
theorem abs_trace_cos_le {n : ℕ} (f : Fin n → Fin n → ℝ) :
    |(Matrix.of fun i j => Real.cos (f i j)).trace| ≤ (n : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin n, |Real.cos (f i i)| ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (n : ℝ) := by simp

end Brockian
#print axioms Brockian.CosTraceNorm2003

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

