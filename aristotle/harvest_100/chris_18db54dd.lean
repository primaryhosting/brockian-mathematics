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

/-
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`, computed
spectrally: it is the sum of `-λ log λ` over the (real) eigenvalues `λ` of `ρ`. -/
noncomputable def vonNeumannEntropy {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : ℝ :=
  ∑ i, Real.negMulLog (hρ.eigenvalues i)

/-- The density matrix `|ψ⟩⟨ψ|` of a state vector `ψ`. -/
def pureDensity (ψ : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec ψ (star ψ)

omit [Fintype n] [DecidableEq n] in
lemma pureDensity_apply (ψ : n → ℂ) (i j : n) :
    pureDensity ψ i j = ψ i * (starRingEnd ℂ) (ψ j) := rfl

/-- `|ψ⟩⟨ψ|` is Hermitian. -/
omit [Fintype n] [DecidableEq n] in
lemma pureDensity_isHermitian (ψ : n → ℂ) : (pureDensity ψ).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, pureDensity_apply, mul_comm]

/-- If `ψ` is a unit vector then `|ψ⟩⟨ψ|` is idempotent. -/
omit [DecidableEq n] in
lemma pureDensity_mul_self {ψ : n → ℂ} (hψ : ∑ i, (starRingEnd ℂ) (ψ i) * ψ i = 1) :
    pureDensity ψ * pureDensity ψ = pureDensity ψ := by
  ext i j
  simp only [Matrix.mul_apply, pureDensity_apply]
  calc ∑ k, ψ i * (starRingEnd ℂ) (ψ k) * (ψ k * (starRingEnd ℂ) (ψ j))
      = (∑ k, (starRingEnd ℂ) (ψ k) * ψ k) * (ψ i * (starRingEnd ℂ) (ψ j)) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = ψ i * (starRingEnd ℂ) (ψ j) := by rw [hψ, one_mul]

/-- The trace of `|ψ⟩⟨ψ|` is `⟨ψ|ψ⟩`. -/
omit [DecidableEq n] in
lemma trace_pureDensity (ψ : n → ℂ) :
    (pureDensity ψ).trace = ∑ i, (starRingEnd ℂ) (ψ i) * ψ i := by
  simp [Matrix.trace, Matrix.diag, pureDensity_apply, mul_comm]

/-- Every eigenvalue of an idempotent Hermitian matrix is idempotent. -/
lemma eigenvalue_sq_of_idempotent {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hidem : A * A = A) (j : n) :
    hA.eigenvalues j ^ 2 = hA.eigenvalues j := by
  set lam := hA.eigenvalues j with hlam
  set v : n → ℂ := (hA.eigenvectorBasis j).ofLp with hv
  have hne : v ≠ 0 := by
    intro h
    have hnorm : ‖hA.eigenvectorBasis j‖ = 1 := hA.eigenvectorBasis.orthonormal.1 j
    have : hA.eigenvectorBasis j = 0 := by
      simpa [hv, WithLp.ofLp_eq_zero] using h
    rw [this] at hnorm
    simp at hnorm
  have h1 : A.mulVec v = lam • v := hA.mulVec_eigenvectorBasis j
  have h2 : A.mulVec (A.mulVec v) = (lam ^ 2) • v := by
    rw [h1, Matrix.mulVec_smul, h1, smul_smul, sq]
  have h3 : A.mulVec (A.mulVec v) = lam • v := by
    rw [Matrix.mulVec_mulVec, hidem, h1]
  have h4 : (lam ^ 2) • v = lam • v := by rw [← h2, h3]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  have := congrFun h4 i
  simp only [Pi.smul_apply, Complex.real_smul] at this
  have hveq : ((lam ^ 2 : ℝ) : ℂ) * v i = ((lam : ℝ) : ℂ) * v i := this
  have hc := mul_right_cancel₀ hi hveq
  exact_mod_cast hc

/-- **Pure states have zero von Neumann entropy.**
If `ψ` is a unit vector (so that the density matrix `ρ = |ψ⟩⟨ψ|` is a pure state, with
`Tr ρ = 1`), then the von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` vanishes. -/
theorem pure_state_zero_entropy {ψ : n → ℂ} (hψ : ∑ i, (starRingEnd ℂ) (ψ i) * ψ i = 1) :
    vonNeumannEntropy (pureDensity_isHermitian ψ) = 0 := by
  have hH := pureDensity_isHermitian ψ
  have hidem := pureDensity_mul_self hψ
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have h := eigenvalue_sq_of_idempotent hH hidem i
  have : hH.eigenvalues i = 0 ∨ hH.eigenvalues i = 1 := by
    rcases mul_eq_zero.1 (show hH.eigenvalues i * (hH.eigenvalues i - 1) = 0 by nlinarith) with
      h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  rcases this with h0 | h1
  · simp [h0, Real.negMulLog]
  · simp [h1, Real.negMulLog]

end QC

