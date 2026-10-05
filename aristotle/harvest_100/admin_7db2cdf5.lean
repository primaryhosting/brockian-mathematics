/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

section CosTraceNorm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute
values of its eigenvalues. -/
noncomputable def hermTraceNorm {A : Matrix n n ℝ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- The cosine Gram matrix of a family of phases `x : n → ℝ`, with entries
`cos (x i - x j)`. -/
noncomputable def cosGram (x : n → ℝ) : Matrix n n ℝ := Matrix.of fun i j => Real.cos (x i - x j)

/-- The `2 × n` matrix whose columns are the unit vectors `(cos (x j), sin (x j))`. -/
noncomputable def phaseFrame (x : n → ℝ) : Matrix (Fin 2) n ℝ :=
  Matrix.of fun k j => if k = 0 then Real.cos (x j) else Real.sin (x j)

omit [Fintype n] [DecidableEq n] in
/-- The cosine Gram matrix factors as `Bᴴ * B` for the phase frame `B`. -/
lemma cosGram_eq_conjTranspose_mul_self (x : n → ℝ) :
    cosGram x = (phaseFrame x)ᴴ * (phaseFrame x) := by
  ext i j
  simp only [cosGram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    phaseFrame, star_trivial]
  rw [Fin.sum_univ_two]
  simp [Real.cos_sub]

omit [DecidableEq n] in
/-- The cosine Gram matrix is positive semidefinite. -/
lemma cosGram_posSemidef (x : n → ℝ) : (cosGram x).PosSemidef := by
  rw [cosGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq n] in
/-- The cosine Gram matrix is Hermitian (i.e. symmetric, over `ℝ`). -/
lemma cosGram_isHermitian (x : n → ℝ) : (cosGram x).IsHermitian :=
  (cosGram_posSemidef x).isHermitian

omit [DecidableEq n] in
/-- The trace of the cosine Gram matrix is the size of the index set. -/
lemma trace_cosGram (x : n → ℝ) :
    (cosGram x).trace = (Fintype.card n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosGram, Finset.card_univ]

/-- **Trace-norm identity for cosine Gram matrices.** For any family of phases,
the trace norm of the matrix `(cos (x i - x j))` equals the number of phases. -/
theorem hermTraceNorm_cosGram (x : n → ℝ) :
    hermTraceNorm (cosGram_isHermitian x) = (Fintype.card n : ℝ) := by
  have hpsd := cosGram_posSemidef x
  have habs : ∀ i, |(cosGram_isHermitian x).eigenvalues i|
      = (cosGram_isHermitian x).eigenvalues i := fun i =>
    abs_of_nonneg (hpsd.eigenvalues_nonneg i)
  have hsum : ∑ i, ((cosGram_isHermitian x).eigenvalues i : ℝ) = (cosGram x).trace :=
    ((cosGram_isHermitian x).trace_eq_sum_eigenvalues).symm
  calc hermTraceNorm (cosGram_isHermitian x)
      = ∑ i, (cosGram_isHermitian x).eigenvalues i := by
        simp only [hermTraceNorm, habs]
    _ = (cosGram x).trace := hsum
    _ = (Fintype.card n : ℝ) := trace_cosGram x

/-- Corollary: the trace norm of a cosine Gram matrix is bounded by the size of the
index set (with equality). -/
theorem hermTraceNorm_cosGram_le (x : n → ℝ) :
    hermTraceNorm (cosGram_isHermitian x) ≤ (Fintype.card n : ℝ) :=
  le_of_eq (hermTraceNorm_cosGram x)

end CosTraceNorm

/-- **Cos Trace Norm 1597.** For any 1597 phases `x : Fin 1597 → ℝ`, the trace norm
(sum of absolute values of eigenvalues) of the positive semidefinite cosine Gram matrix
`M i j = cos (x i - x j)` equals `1597`. -/
theorem CosTraceNorm1597 (x : Fin 1597 → ℝ) :
    hermTraceNorm (cosGram_isHermitian x) = 1597 := by
  rw [hermTraceNorm_cosGram x]
  simp

end Brockian

#print axioms Brockian.CosTraceNorm1597

