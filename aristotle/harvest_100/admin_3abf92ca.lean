/-
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Matrix
open scoped MatrixOrder

/-- The `4001 × 4001` real "cosine Gram matrix" attached to a family of angles
`θ : Fin 4001 → ℝ`, with entries `cos (θ i - θ j)`. -/
noncomputable def cosGram (θ : Fin 4001 → ℝ) : Matrix (Fin 4001) (Fin 4001) ℝ :=
  fun i j => Real.cos (θ i - θ j)

/-- The `2 × 4001` matrix whose columns are the unit vectors `(cos θ j, sin θ j)`. -/
noncomputable def angleFrame (θ : Fin 4001 → ℝ) : Matrix (Fin 2) (Fin 4001) ℝ :=
  fun k j => if k = 0 then Real.cos (θ j) else Real.sin (θ j)

/-- The trace norm (Schatten 1-norm) of a real square matrix: the trace of the positive
semidefinite square root of `Mᴴ * M`, i.e. the sum of the singular values of `M`. -/
noncomputable def traceNorm {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : ℝ :=
  (CFC.sqrt (Mᴴ * M)).trace

/-- The cosine Gram matrix factors as `Bᴴ * B` for the frame of unit vectors
`(cos θ j, sin θ j)`. -/
theorem cosGram_eq_conjTranspose_mul_self (θ : Fin 4001 → ℝ) :
    cosGram θ = (angleFrame θ)ᴴ * (angleFrame θ) := by
  ext i j
  simp [cosGram, angleFrame, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub]

/-- The cosine Gram matrix is positive semidefinite. -/
theorem cosGram_posSemidef (θ : Fin 4001 → ℝ) : (cosGram θ).PosSemidef := by
  rw [cosGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The trace of the cosine Gram matrix is `4001`. -/
theorem trace_cosGram (θ : Fin 4001 → ℝ) : (cosGram θ).trace = 4001 := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 4001.**  For every family of angles `θ : Fin 4001 → ℝ`, the
`4001 × 4001` cosine Gram matrix `(cos (θ i - θ j))` has trace norm exactly `4001`. -/
theorem CosTraceNorm4001 (θ : Fin 4001 → ℝ) : traceNorm (cosGram θ) = 4001 := by
  have hpsd := cosGram_posSemidef θ
  have hherm : (cosGram θ)ᴴ = cosGram θ := hpsd.isHermitian
  have hsq : (cosGram θ)ᴴ * (cosGram θ) = (cosGram θ) ^ 2 := by
    rw [hherm, pow_two]
  rw [traceNorm, hsq, CFC.sqrt_sq _ hpsd.nonneg, trace_cosGram]

end Brockian

namespace Brockian

/-- Trace-norm bound form: the cosine Gram matrix of any `4001` angles has trace norm
at most (indeed exactly) `4001`. -/
theorem cosTraceNorm4001_le (θ : Fin 4001 → ℝ) : traceNorm (cosGram θ) ≤ 4001 :=
  le_of_eq (CosTraceNorm4001 θ)

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

