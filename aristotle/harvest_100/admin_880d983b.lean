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

/-- The `n × n` real "cosine Gram matrix" of a family of angles `θ`, with entries
`cos (θ i - θ j)`. -/
noncomputable def cosGram (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The `2 × n` factor whose columns are the unit vectors `(cos (θ j), sin (θ j))`. -/
noncomputable def cosFactor (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k j => if k = 0 then Real.cos (θ j) else Real.sin (θ j)

/-- The cosine Gram matrix is indeed a Gram matrix: `cosGram n θ = Bᴴ * B`. -/
theorem cosGram_eq_conjTranspose_mul_self (n : ℕ) (θ : Fin n → ℝ) :
    cosGram n θ = (Matrix.conjTranspose (cosFactor n θ)) * (cosFactor n θ) := by
  ext i j
  simp [cosGram, cosFactor, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub]

/-- The cosine Gram matrix is positive semidefinite. -/
theorem cosGram_posSemidef (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).PosSemidef := by
  rw [cosGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The cosine Gram matrix is Hermitian (i.e. symmetric, as it is real). -/
theorem cosGram_isHermitian (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).IsHermitian :=
  (cosGram_posSemidef n θ).isHermitian

/-- The trace of the cosine Gram matrix is `n`. -/
theorem cosGram_trace (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).trace = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosGram]

/-- **Cos Trace Norm 1279.**  For any family of angles `θ : Fin n → ℝ`, the trace norm
(the sum of the absolute values of the eigenvalues, equivalently the sum of the singular
values) of the cosine Gram matrix `(cos (θ i - θ j))ᵢⱼ` equals `n`. -/
theorem CosTraceNorm1279 (n : ℕ) (θ : Fin n → ℝ) :
    ∑ i, |(cosGram_isHermitian n θ).eigenvalues i| = (n : ℝ) := by
  have hnn : ∀ i, 0 ≤ (cosGram_isHermitian n θ).eigenvalues i := fun i =>
    (cosGram_posSemidef n θ).eigenvalues_nonneg i
  have : ∑ i, |(cosGram_isHermitian n θ).eigenvalues i|
      = ∑ i, (cosGram_isHermitian n θ).eigenvalues i :=
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hnn i)
  have htr := (cosGram_isHermitian n θ).trace_eq_sum_eigenvalues
  rw [cosGram_trace] at htr
  rw [this]
  exact_mod_cast htr.symm

end Brockian

