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


open scoped BigOperators
open scoped Matrix

set_option maxRecDepth 10000

namespace Brockian

/-- The `n × n` real "cosine Gram matrix" with entries `cos (i θ - j θ)`. -/
noncomputable def cosGram (n : ℕ) (theta : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos ((i : ℝ) * theta - (j : ℝ) * theta)

/-- The `2 × n` matrix whose columns are the unit vectors `(cos (j θ), sin (j θ))`. -/
noncomputable def cosSinRows (n : ℕ) (theta : ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun i j => if i = 0 then Real.cos ((j : ℝ) * theta) else Real.sin ((j : ℝ) * theta)

/-- The cosine Gram matrix is the Gram matrix of the columns of `cosSinRows`. -/
theorem cosGram_eq_conjTranspose_mul_self (n : ℕ) (theta : ℝ) :
    cosGram n theta = (cosSinRows n theta)ᴴ * (cosSinRows n theta) := by
  ext i j
  simp [cosGram, cosSinRows, Matrix.mul_apply,
    Fin.sum_univ_two, Real.cos_sub, mul_comm]

/-- The cosine Gram matrix is positive semidefinite. -/
theorem cosGram_posSemidef (n : ℕ) (theta : ℝ) : (cosGram n theta).PosSemidef := by
  rw [cosGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The cosine Gram matrix is Hermitian (i.e. symmetric, being real). -/
theorem cosGram_isHermitian (n : ℕ) (theta : ℝ) : (cosGram n theta).IsHermitian :=
  (cosGram_posSemidef n theta).1

/-- The trace of the `n × n` cosine Gram matrix is `n`. -/
theorem cosGram_trace (n : ℕ) (theta : ℝ) : (cosGram n theta).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **General form.** For every `n` and every angle `θ`, the trace norm (sum of the absolute
values of the eigenvalues) of the `n × n` matrix `cos (i θ - j θ)` equals `n`. -/
theorem cosGram_traceNorm (n : ℕ) (theta : ℝ) :
    ∑ i, |(cosGram_isHermitian n theta).eigenvalues i| = n := by
  have hpos := cosGram_posSemidef n theta
  have h1 : ∑ i, |(cosGram_isHermitian n theta).eigenvalues i|
      = ∑ i, (cosGram_isHermitian n theta).eigenvalues i :=
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hpos.eigenvalues_nonneg i)
  have h2 := (cosGram_isHermitian n theta).trace_eq_sum_eigenvalues
  rw [cosGram_trace] at h2
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h2
  rw [h1, ← h2]

/--
**Cos Trace Norm 4001.**

The trace norm (Schatten 1-norm, i.e. the sum of the absolute values of the eigenvalues) of
the `4001 × 4001` matrix with entries `cos (i θ - j θ)` equals `4001`, for every angle `θ`.

The matrix is a Gram matrix of unit vectors in the plane, hence positive semidefinite, so its
trace norm coincides with its trace, which is `4001`.
-/
theorem CosTraceNorm4001 (theta : ℝ) :
    ∑ i, |(cosGram_isHermitian 4001 theta).eigenvalues i| = 4001 := by
  simpa using cosGram_traceNorm 4001 theta

/-- The corresponding trace-norm bound: the trace norm is at most `4001`. -/
theorem CosTraceNorm4001_le (theta : ℝ) :
    ∑ i, |(cosGram_isHermitian 4001 theta).eigenvalues i| ≤ 4001 :=
  le_of_eq (CosTraceNorm4001 theta)

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

