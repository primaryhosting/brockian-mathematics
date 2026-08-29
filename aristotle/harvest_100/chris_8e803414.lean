/-
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QPhys

open scoped InnerProductSpace

/-- Key computation: if `T` is symmetric (Hermitian) and `T v = μ • v` with `v ≠ 0`,
then `conj μ = μ`. -/
theorem conj_eigenvalue_eq_self_of_isSymmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    {μ : ℂ} {v : E} (hv : v ≠ 0) (hTv : T v = μ • v) :
    (starRingEnd ℂ) μ = μ := by
  have key : (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
    have h := hT v v
    rw [hTv] at h
    rw [inner_smul_left, inner_smul_right] at h
    exact h
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  exact mul_right_cancel₀ hvv key

/-- **Every eigenvalue of a Hermitian operator is real.**

If `T` is a Hermitian (symmetric) linear operator on a complex inner product space and
`μ` is an eigenvalue of `T` (i.e. `T v = μ • v` for some nonzero vector `v`), then `μ`
is a real number: it has zero imaginary part, and indeed equals the coercion of a real. -/
theorem hermitian_real_spectrum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    {μ : ℂ} {v : E} (hv : v ≠ 0) (hTv : T v = μ • v) :
    μ.im = 0 ∧ ∃ r : ℝ, μ = (r : ℂ) := by
  have h := conj_eigenvalue_eq_self_of_isSymmetric hT hv hTv
  have him : μ.im = 0 := by
    have := congrArg Complex.im h
    simp [Complex.conj_im] at this
    linarith
  exact ⟨him, ⟨μ.re, by apply Complex.ext <;> simp [him]⟩⟩

/-- Matrix form: every eigenvalue of a Hermitian matrix is real. -/
theorem hermitian_matrix_real_spectrum
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {μ : ℂ} {v : n → ℂ} (hv : v ≠ 0) (hAv : A.mulVec v = μ • v) :
    μ.im = 0 ∧ ∃ r : ℝ, μ = (r : ℂ) := by
  have hconj : ∀ i j, (starRingEnd ℂ) (A i j) = A j i := by
    intro i j
    have := congrFun (congrFun hA.eq j) i
    simpa [Matrix.conjTranspose_apply] using this
  have hmv : ∀ i, A.mulVec v i = ∑ j, A i j * v j := by
    intro i; simp [Matrix.mulVec, dotProduct]
  have hs : (∑ i, (starRingEnd ℂ) (v i) * v i) ≠ 0 := by
    have hcast : (∑ i, (starRingEnd ℂ) (v i) * v i)
        = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Complex.normSq_eq_conj_mul_self]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have hpos : 0 < ∑ i, Complex.normSq (v i) := by
      refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
      simpa [Complex.normSq_pos] using hi
    rw [hcast, Ne, Complex.ofReal_eq_zero]
    exact hpos.ne'
  have e3 : ∑ i, (starRingEnd ℂ) (v i) * (A.mulVec v i)
      = ∑ i, (starRingEnd ℂ) (A.mulVec v i) * v i := by
    simp only [hmv, map_sum, map_mul, hconj, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e1 : ∑ i, (starRingEnd ℂ) (v i) * (A.mulVec v i)
      = μ * ∑ i, (starRingEnd ℂ) (v i) * v i := by
    rw [hAv]; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (starRingEnd ℂ) (A.mulVec v i) * v i
      = (starRingEnd ℂ) μ * ∑ i, (starRingEnd ℂ) (v i) * v i := by
    rw [hAv]; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hmc : μ = (starRingEnd ℂ) μ := mul_right_cancel₀ hs (by rw [← e1, ← e2, e3])
  have him := congrArg Complex.im hmc
  simp [Complex.conj_im] at him
  have him0 : μ.im = 0 := by linarith
  exact ⟨him0, μ.re, by apply Complex.ext <;> simp [him0]⟩

end QPhys

#print axioms QPhys.hermitian_real_spectrum
#print axioms QPhys.hermitian_matrix_real_spectrum

