/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Brockian

/-- The `n × n` real "cosine Gram" matrix attached to a family of phases `x : Fin n → ℝ`,
with entries `cos (x i - x j)`. -/
noncomputable def cosGram (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (x i - x j)

/-- The `2 × n` matrix whose columns are the unit vectors `(cos (x j), sin (x j))`. -/
noncomputable def cosFactor (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k j => if k = 0 then Real.cos (x j) else Real.sin (x j)

lemma cosGram_eq_factor (n : ℕ) (x : Fin n → ℝ) :
    (cosFactor n x)ᴴ * cosFactor n x = cosGram n x := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cosFactor, cosGram, Matrix.of_apply,
    star_trivial]
  rw [Fin.sum_univ_two]
  simp [Real.cos_sub]

/-- The cosine Gram matrix is positive semidefinite (it is a genuine Gram matrix). -/
lemma cosGram_posSemidef (n : ℕ) (x : Fin n → ℝ) : (cosGram n x).PosSemidef := by
  rw [← cosGram_eq_factor n x]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma cosGram_isHermitian (n : ℕ) (x : Fin n → ℝ) : (cosGram n x).IsHermitian :=
  (cosGram_posSemidef n x).isHermitian

lemma cosGram_trace (n : ℕ) (x : Fin n → ℝ) : (cosGram n x).trace = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 3499.**  For any family of phases `x : Fin n → ℝ`, the trace norm
(the sum of the absolute values of the eigenvalues) of the cosine Gram matrix
`A i j = cos (x i - x j)` is exactly `n`.  In particular the trace norm is bounded by `n`,
this bound being attained. -/
theorem CosTraceNorm3499 (n : ℕ) (x : Fin n → ℝ) :
    ∑ i, |(cosGram_isHermitian n x).eigenvalues i| = (n : ℝ) := by
  have hnn : ∀ i, 0 ≤ (cosGram_isHermitian n x).eigenvalues i := fun i => by
    have := (cosGram_posSemidef n x).eigenvalues_nonneg i
    simpa using this
  have habs : ∀ i, |(cosGram_isHermitian n x).eigenvalues i|
      = (cosGram_isHermitian n x).eigenvalues i := fun i => abs_of_nonneg (hnn i)
  calc ∑ i, |(cosGram_isHermitian n x).eigenvalues i|
      = ∑ i, (cosGram_isHermitian n x).eigenvalues i := by
        exact Finset.sum_congr rfl fun i _ => habs i
    _ = (cosGram n x).trace := by
        rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues (cosGram_isHermitian n x)]
        norm_num
    _ = (n : ℝ) := cosGram_trace n x

end Brockian

#print axioms Brockian.CosTraceNorm3499

