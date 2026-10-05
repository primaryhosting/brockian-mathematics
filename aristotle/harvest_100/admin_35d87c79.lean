/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The "cosine kernel" matrix `C i j = cos (x i - x j)` attached to phases `x : Fin n → ℝ`. -/
noncomputable def cosMatrix {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.cos (x i - x j)

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute values of
its eigenvalues. -/
noncomputable def traceNorm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- The `2 × n` matrix whose columns are the unit vectors `(cos (x i), sin (x i))`. -/
noncomputable def phaseFrame {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  fun k i => if k = 0 then Real.cos (x i) else Real.sin (x i)

lemma cosMatrix_eq_gram {n : ℕ} (x : Fin n → ℝ) :
    cosMatrix x = Matrix.conjTranspose (phaseFrame x) * phaseFrame x := by
  ext i j
  simp only [cosMatrix, phaseFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Real.cos_sub, star_trivial]
  norm_num

lemma cosMatrix_posSemidef {n : ℕ} (x : Fin n → ℝ) : (cosMatrix x).PosSemidef := by
  rw [cosMatrix_eq_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma cosMatrix_trace {n : ℕ} (x : Fin n → ℝ) : (cosMatrix x).trace = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosMatrix]

/--
**Cos Trace Norm 1597.**  For any phases `x : Fin n → ℝ`, the cosine-kernel matrix
`C i j = cos (x i - x j)` is positive semidefinite, and consequently its trace norm
(the sum of the absolute values of its eigenvalues) equals its trace, namely `n`.
-/
theorem CosTraceNorm1597 {n : ℕ} (x : Fin n → ℝ) (h : (cosMatrix x).IsHermitian) :
    (cosMatrix x).PosSemidef ∧ traceNorm h = (n : ℝ) := by
  refine ⟨cosMatrix_posSemidef x, ?_⟩
  have hpsd := cosMatrix_posSemidef x
  have hnn : ∀ i, 0 ≤ h.eigenvalues i := fun i => hpsd.eigenvalues_nonneg i
  have habs : traceNorm h = ∑ i, h.eigenvalues i :=
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hnn i)
  have ht : (cosMatrix x).trace = ∑ i, h.eigenvalues i := by
    simpa using h.trace_eq_sum_eigenvalues
  rw [habs, ← ht, cosMatrix_trace]

/-- The `n = 1597` instance: the cosine kernel of 1597 phases has trace norm `1597`. -/
theorem CosTraceNorm1597_dim (x : Fin 1597 → ℝ) (h : (cosMatrix x).IsHermitian) :
    traceNorm h = 1597 := by
  simpa using (CosTraceNorm1597 x h).2

#print axioms Brockian.CosTraceNorm1597
#print axioms Brockian.CosTraceNorm1597_dim

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

