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

/-- The cosine Gram matrix of a family of angles: `C i j = cos (θ i - θ j)`. -/
noncomputable def cosGram (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The `2 × n` matrix whose columns are the unit vectors `(cos θ j, sin θ j)`. -/
noncomputable def cosSinRows (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k j => if k = 0 then Real.cos (θ j) else Real.sin (θ j)

/-- Key factorization: the cosine Gram matrix is the Gram matrix of the planar unit vectors
`(cos θ j, sin θ j)`, i.e. `C = Bᴴ * B` with `B = cosSinRows`. -/
theorem cosGram_eq_conjTranspose_mul_self (n : ℕ) (θ : Fin n → ℝ) :
    cosGram n θ = (cosSinRows n θ).conjTranspose * (cosSinRows n θ) := by
  ext i j
  simp [cosGram, cosSinRows, Matrix.mul_apply,
    Fin.sum_univ_two, Real.cos_sub, mul_comm]

/-- Key intermediate lemma: the cosine Gram matrix is positive semidefinite. -/
theorem cosGram_posSemidef (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).PosSemidef := by
  rw [cosGram_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The trace of the cosine Gram matrix is `n`, since its diagonal entries are `cos 0 = 1`. -/
theorem trace_cosGram (n : ℕ) (θ : Fin n → ℝ) : (cosGram n θ).trace = (n : ℝ) := by
  simp [cosGram, Matrix.trace, Matrix.diag]

/--
**Cos Trace Norm 1279.**

For any family of angles `θ : Fin n → ℝ`, the trace (nuclear) norm of the cosine Gram matrix
`C i j = cos (θ i - θ j)`, i.e. the sum of the absolute values of its (real) eigenvalues,
equals exactly `n`.  Consequently it also satisfies the sharp bound `‖C‖_* ≤ n`.
-/
theorem CosTraceNorm1279 (n : ℕ) (θ : Fin n → ℝ) (h : (cosGram n θ).IsHermitian) :
    ∑ i, |h.eigenvalues i| = (n : ℝ) ∧ ∑ i, |h.eigenvalues i| ≤ (n : ℝ) := by
  have hpsd : (cosGram n θ).PosSemidef := cosGram_posSemidef n θ
  have hnn : ∀ i, 0 ≤ h.eigenvalues i := by
    intro i
    have := hpsd.eigenvalues_nonneg i
    simpa using this
  have habs : ∑ i, |h.eigenvalues i| = ∑ i, h.eigenvalues i :=
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hnn i)
  have htr : (cosGram n θ).trace = ∑ i, h.eigenvalues i := by
    simpa using h.trace_eq_sum_eigenvalues
  have : ∑ i, |h.eigenvalues i| = (n : ℝ) := by
    rw [habs, ← htr, trace_cosGram]
  exact ⟨this, le_of_eq this⟩

end Brockian

