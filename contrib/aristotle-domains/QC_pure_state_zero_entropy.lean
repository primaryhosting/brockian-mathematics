/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Statement: The von Neumann entropy S(ρ)= -Tr(ρ log ρ) of a pure state is 0.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

open scoped Matrix

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`, computed
spectrally: since `ρ` is Hermitian it is unitarily diagonalizable with real eigenvalues
`λ i`, and `-Tr(ρ log ρ) = -∑ i, λ i * log (λ i)`.  (As usual `0 * log 0 = 0`, which is
automatic with Mathlib's convention `Real.log 0 = 0`.) -/
noncomputable def vonNeumannEntropy {rho : Matrix n n ℂ} (hrho : rho.IsHermitian) : ℝ :=
  -∑ i, hrho.eigenvalues i * Real.log (hrho.eigenvalues i)

/-- The density matrix `|ψ⟩⟨ψ|` of the (column) vector `ψ`. -/
def pureState (psi : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec psi (star psi)

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem pureState_apply (psi : n → ℂ) (i j : n) :
    pureState psi i j = psi i * (starRingEnd ℂ) (psi j) := rfl

omit [Fintype n] [DecidableEq n] in
/-- `|ψ⟩⟨ψ|` is Hermitian. -/
theorem isHermitian_pureState (psi : n → ℂ) : (pureState psi).IsHermitian := by
  ext i j
  simp [pureState, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]

omit [DecidableEq n] in
/-- A normalized vector gives a density matrix of unit trace. -/
theorem trace_pureState (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    (pureState psi).trace = 1 := by
  have h : ∀ i : n, psi i * (starRingEnd ℂ) (psi i) = ((‖psi i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Matrix.trace, Matrix.diag_apply, pureState_apply, h]
  rw [← Complex.ofReal_sum, hpsi, Complex.ofReal_one]

omit [DecidableEq n] in
/-- A normalized vector gives an idempotent density matrix: `|ψ⟩⟨ψ|` is a projection. -/
theorem pureState_mul_self (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    pureState psi * pureState psi = pureState psi := by
  have h : ∀ i : n, (starRingEnd ℂ) (psi i) * psi i = ((‖psi i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  ext i j
  simp only [Matrix.mul_apply, pureState_apply]
  calc ∑ k : n, psi i * (starRingEnd ℂ) (psi k) * (psi k * (starRingEnd ℂ) (psi j))
      = (∑ k : n, ((‖psi k‖ ^ 2 : ℝ) : ℂ)) * (psi i * (starRingEnd ℂ) (psi j)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← h k]; ring
    _ = psi i * (starRingEnd ℂ) (psi j) := by
        rw [← Complex.ofReal_sum, hpsi, Complex.ofReal_one, one_mul]

/-- The eigenvalues of a Hermitian idempotent matrix (an orthogonal projection) are `0` or `1`. -/
theorem eigenvalues_eq_zero_or_one_of_idempotent {rho : Matrix n n ℂ} (hrho : rho.IsHermitian)
    (hidem : rho * rho = rho) (i : n) :
    hrho.eigenvalues i = 0 ∨ hrho.eigenvalues i = 1 := by
  set v : n → ℂ := ⇑(hrho.eigenvectorBasis i) with hv
  have hvne : v ≠ 0 := by
    have := hrho.eigenvectorBasis.orthonormal.ne_zero i
    simpa [hv] using this
  have h1 : rho *ᵥ v = (hrho.eigenvalues i) • v := hrho.mulVec_eigenvectorBasis i
  have h2 : rho *ᵥ (rho *ᵥ v) = (hrho.eigenvalues i) • v := by
    rw [Matrix.mulVec_mulVec, hidem, h1]
  have h3 : rho *ᵥ (rho *ᵥ v) = ((hrho.eigenvalues i) * (hrho.eigenvalues i)) • v := by
    rw [h1, Matrix.mulVec_smul, h1, smul_smul]
  have h4 : ((hrho.eigenvalues i) * (hrho.eigenvalues i)) • v = (hrho.eigenvalues i) • v := by
    rw [← h3, h2]
  obtain ⟨j, hj⟩ : ∃ j : n, v j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hvne (funext hcon)
  have h5 : (hrho.eigenvalues i) * (hrho.eigenvalues i) = hrho.eigenvalues i := by
    have hthis := congrFun h4 j
    simp only [Pi.smul_apply, Complex.real_smul] at hthis
    exact_mod_cast mul_right_cancel₀ hj hthis
  rcases eq_or_ne (hrho.eigenvalues i) 0 with h | h
  · exact Or.inl h
  · exact Or.inr (mul_right_cancel₀ h (by rw [one_mul]; exact h5))

/-- The von Neumann entropy of a Hermitian projection vanishes. -/
theorem entropy_eq_zero_of_idempotent {rho : Matrix n n ℂ} (hrho : rho.IsHermitian)
    (hidem : rho * rho = rho) :
    vonNeumannEntropy hrho = 0 := by
  have : ∀ i : n, hrho.eigenvalues i * Real.log (hrho.eigenvalues i) = 0 := by
    intro i
    rcases eigenvalues_eq_zero_or_one_of_idempotent hrho hidem i with h | h
    · rw [h, zero_mul]
    · rw [h, Real.log_one, mul_zero]
  simp [vonNeumannEntropy, this]

/-- **The von Neumann entropy of a pure state vanishes.**
For a normalized vector `ψ`, the density matrix `ρ = |ψ⟩⟨ψ|` satisfies `S(ρ) = -Tr(ρ log ρ) = 0`. -/
theorem pure_state_zero_entropy (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    vonNeumannEntropy (isHermitian_pureState psi) = 0 :=
  entropy_eq_zero_of_idempotent (isHermitian_pureState psi) (pureState_mul_self psi hpsi)

end QC

