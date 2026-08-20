import Mathlib

/-!
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix
open scoped MatrixOrder

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

/-- The trace norm (Schatten 1-norm, i.e. the sum of the singular values) of a square
matrix `A`, defined as `tr √(Aᴴ * A)`. -/
noncomputable def traceNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : ℝ :=
  (CFC.sqrt (Aᴴ * A)).trace

/-- The "cosine kernel" matrix `C i j = cos (θ i - θ j)`. -/
noncomputable def cosMatrix {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The `2 × n` matrix whose columns are the unit vectors `(cos θ i, sin θ i)`. -/
noncomputable def cosSinMatrix {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k i => if k = 0 then Real.cos (θ i) else Real.sin (θ i)

/-- The cosine kernel matrix is the Gram matrix of the unit vectors `(cos θ i, sin θ i)`. -/
theorem cosMatrix_eq_gram {n : ℕ} (θ : Fin n → ℝ) :
    cosMatrix θ = (cosSinMatrix θ)ᴴ * cosSinMatrix θ := by
  ext i j
  simp [cosMatrix, cosSinMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub, mul_comm]

/-- The cosine kernel matrix is positive semidefinite. -/
theorem cosMatrix_posSemidef {n : ℕ} (θ : Fin n → ℝ) : (cosMatrix θ).PosSemidef := by
  rw [cosMatrix_eq_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The trace of the cosine kernel matrix is `n`. -/
theorem cosMatrix_trace {n : ℕ} (θ : Fin n → ℝ) : (cosMatrix θ).trace = n := by
  simp [cosMatrix, Matrix.trace, Matrix.diag]

/-- **Cos Trace Norm 3499.**  For any phases `θ : Fin n → ℝ`, the trace norm (sum of the
singular values) of the cosine kernel matrix `C i j = cos (θ i - θ j)` equals `n`; in
particular it is bounded by `n`. -/
theorem CosTraceNorm3499 {n : ℕ} (θ : Fin n → ℝ) :
    traceNorm (cosMatrix θ) = n ∧ traceNorm (cosMatrix θ) ≤ n := by
  have hpsd : (cosMatrix θ).PosSemidef := cosMatrix_posSemidef θ
  have hherm : (cosMatrix θ)ᴴ = cosMatrix θ := hpsd.isHermitian
  have hsq : (cosMatrix θ)ᴴ * cosMatrix θ = (cosMatrix θ) ^ 2 := by
    rw [hherm, sq]
  have hsqrt : CFC.sqrt ((cosMatrix θ)ᴴ * cosMatrix θ) = cosMatrix θ := by
    rw [hsq, CFC.sqrt_sq (a := cosMatrix θ) hpsd.nonneg]
  have heq : traceNorm (cosMatrix θ) = n := by
    rw [traceNorm, hsqrt, cosMatrix_trace]
  exact ⟨heq, le_of_eq heq⟩

end Brockian

