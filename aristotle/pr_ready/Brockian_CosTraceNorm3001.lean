/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not permit a
-- module docstring before `import`; the module docstring is repeated after the imports.)


/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
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

set_option grind.warning false

namespace Brockian

/-- The `2 × n` real matrix whose `i`-th column is the unit vector
`(cos (θ i), sin (θ i))`. -/
noncomputable def cosGramFactor {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k i => if k = 0 then Real.cos (θ i) else Real.sin (θ i)

/-- The real `n × n` "cosine kernel" matrix with entries `cos (θ i - θ j)`. -/
noncomputable def cosMatrix {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The cosine kernel matrix is the Gram matrix of the planar unit vectors
`(cos (θ i), sin (θ i))`, by the cosine subtraction formula. -/
lemma cosGramFactor_conjTranspose_mul_self {n : ℕ} (θ : Fin n → ℝ) :
    (cosGramFactor θ)ᴴ * (cosGramFactor θ) = cosMatrix θ := by
  ext i j
  simp [Matrix.mul_apply, cosGramFactor, cosMatrix, Fin.sum_univ_two, Real.cos_sub]

/-- The cosine kernel matrix is positive semidefinite: it is a Gram matrix
(`Matrix.posSemidef_conjTranspose_mul_self`). -/
lemma cosMatrix_posSemidef {n : ℕ} (θ : Fin n → ℝ) : (cosMatrix θ).PosSemidef := by
  rw [← cosGramFactor_conjTranspose_mul_self θ]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The cosine kernel matrix is (real) symmetric, hence Hermitian; so the hypothesis of
`CosTraceNorm3001` is always satisfiable. -/
lemma cosMatrix_isHermitian {n : ℕ} (θ : Fin n → ℝ) : (cosMatrix θ).IsHermitian :=
  (cosMatrix_posSemidef θ).isHermitian

/-- The diagonal entries of the cosine kernel matrix are `cos 0 = 1`, so its trace is `n`. -/
lemma cosMatrix_trace {n : ℕ} (θ : Fin n → ℝ) : (cosMatrix θ).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosMatrix]

/--
**Cos Trace Norm 3001.**

For any phases `θ : Fin n → ℝ`, the trace norm (Schatten `1`-norm, i.e. the sum of the
absolute values of the eigenvalues of this symmetric matrix, which are its singular values)
of the cosine kernel matrix `M i j = cos (θ i - θ j)` equals `n`.

The matrix is positive semidefinite, being the Gram matrix of the unit vectors
`(cos (θ i), sin (θ i))`, so its trace norm coincides with its trace, which is `n`
since every diagonal entry is `cos 0 = 1`.

Key Mathlib ingredients: `Matrix.posSemidef_conjTranspose_mul_self`,
`Matrix.PosSemidef.eigenvalues_nonneg`, `Matrix.IsHermitian.trace_eq_sum_eigenvalues`.
-/
theorem CosTraceNorm3001 {n : ℕ} (θ : Fin n → ℝ)
    (hH : (cosMatrix θ).IsHermitian) :
    ∑ i, |hH.eigenvalues i| = (n : ℝ) := by
  have hpsd := cosMatrix_posSemidef θ
  have h1 : ∀ i, |hH.eigenvalues i| = hH.eigenvalues i := fun i =>
    abs_of_nonneg (hpsd.eigenvalues_nonneg i)
  simp only [h1]
  have htr := hH.trace_eq_sum_eigenvalues
  rw [cosMatrix_trace] at htr
  exact_mod_cast htr.symm

end Brockian

