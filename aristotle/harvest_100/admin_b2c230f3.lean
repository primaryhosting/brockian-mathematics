import Mathlib

/-!
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Matrix
open scoped ComplexOrder MatrixOrder

/-- The trace norm (Schatten 1-norm) of a complex square matrix:
the trace of the positive square root of `Aᴴ * A`. -/
noncomputable def traceNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ℝ :=
  (CFC.sqrt (Aᴴ * A)).trace.re

/-- The cosine Gram matrix of a family of angles: `C i j = cos (θ i - θ j)`. -/
noncomputable def cosGram (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ((Real.cos (θ i - θ j) : ℝ) : ℂ)

/-- The matrix of unit vectors `(cos θ i, sin θ i)` whose Gram matrix is `cosGram`. -/
noncomputable def circlePoints (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin 2) ℂ :=
  Matrix.of fun i k => if k = 0 then ((Real.cos (θ i) : ℝ) : ℂ) else ((Real.sin (θ i) : ℝ) : ℂ)

/-- The cosine Gram matrix is a genuine Gram matrix: `C = M * Mᴴ`. -/
theorem cosGram_eq_mul_conjTranspose (n : ℕ) (θ : Fin n → ℝ) :
    cosGram n θ = circlePoints n θ * (circlePoints n θ)ᴴ := by
  ext i j
  simp [cosGram, circlePoints, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub,
    Matrix.conjTranspose_apply, Complex.conj_ofReal]
  push_cast
  ring

/-- The cosine Gram matrix is positive semidefinite. -/
theorem cosGram_posSemidef (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).PosSemidef := by
  rw [cosGram_eq_mul_conjTranspose]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The trace of the cosine Gram matrix is `n`. -/
theorem cosGram_trace (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).trace = (n : ℂ) := by
  simp [Matrix.trace, cosGram, Matrix.diag]

/-- **Cos Trace Norm 3499.**  For any family of angles `θ : Fin n → ℝ`, the trace norm
(Schatten 1-norm) of the cosine Gram matrix `C i j = cos (θ i - θ j)` is exactly `n`;
in particular it is bounded by `n`, the bound being attained for every choice of angles. -/
theorem CosTraceNorm3499 (n : ℕ) (θ : Fin n → ℝ) :
    traceNorm (cosGram n θ) = (n : ℝ) ∧ traceNorm (cosGram n θ) ≤ (n : ℝ) := by
  have hpsd := cosGram_posSemidef n θ
  have hsq : (cosGram n θ)ᴴ * (cosGram n θ) = (cosGram n θ) ^ 2 := by
    rw [hpsd.isHermitian.eq, sq]
  have hkey : traceNorm (cosGram n θ) = (n : ℝ) := by
    rw [traceNorm, hsq, CFC.sqrt_sq _ hpsd.nonneg, cosGram_trace]
    simp
  exact ⟨hkey, le_of_eq hkey⟩

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

