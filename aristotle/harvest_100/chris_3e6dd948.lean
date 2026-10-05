/-
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- The circular (cosine) Gram matrix of a family of angles `θ : Fin n → ℝ`:
its `(i, j)` entry is `cos (θ i - θ j)`. -/
noncomputable def cosGram (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The `2 × n` matrix whose columns are the unit vectors `(cos (θ i), sin (θ i))`. -/
noncomputable def circleFrame (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k i => if k = 0 then Real.cos (θ i) else Real.sin (θ i)

/-- The cosine Gram matrix is the Gram matrix of the unit vectors on the circle. -/
theorem cosGram_eq_conjTranspose_mul_self (n : ℕ) (θ : Fin n → ℝ) :
    cosGram n θ = (circleFrame n θ)ᴴ * (circleFrame n θ) := by
  ext i j
  simp only [cosGram, circleFrame, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_trivial, Fin.sum_univ_two]
  norm_num [Real.cos_sub, mul_comm]

/-- The cosine Gram matrix is positive semidefinite. -/
theorem cosGram_posSemidef (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).PosSemidef := by
  rw [cosGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The trace of the cosine Gram matrix is `n`. -/
theorem trace_cosGram (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- General form: for any `n` angles, the trace norm (sum of absolute values of the
eigenvalues) of the cosine Gram matrix equals `n`. -/
theorem cosGram_traceNorm (n : ℕ) (θ : Fin n → ℝ) :
    ∑ i, |(cosGram_posSemidef n θ).isHermitian.eigenvalues i| = n := by
  have hpsd := cosGram_posSemidef n θ
  calc ∑ i, |hpsd.isHermitian.eigenvalues i|
      = ∑ i, hpsd.isHermitian.eigenvalues i :=
        Finset.sum_congr rfl fun i _ => abs_of_nonneg (hpsd.eigenvalues_nonneg i)
    _ = (cosGram n θ).trace := hpsd.isHermitian.trace_eq_sum_eigenvalues.symm
    _ = n := trace_cosGram n θ

/-- **Cos Trace Norm 1279.**
For any family of `1279` angles `θ`, the cosine Gram matrix `A i j = cos (θ i - θ j)` is
positive semidefinite, has trace `1279`, and its trace norm (the sum of the absolute values
of its eigenvalues, equivalently the sum of its singular values) is exactly `1279`. -/
theorem CosTraceNorm1279 (θ : Fin 1279 → ℝ) :
    (cosGram 1279 θ).PosSemidef ∧ (cosGram 1279 θ).trace = 1279 ∧
      ∑ i, |(cosGram_posSemidef 1279 θ).isHermitian.eigenvalues i| = 1279 := by
  refine ⟨cosGram_posSemidef 1279 θ, by simpa using trace_cosGram 1279 θ, ?_⟩
  simpa using cosGram_traceNorm 1279 θ

end Brockian

