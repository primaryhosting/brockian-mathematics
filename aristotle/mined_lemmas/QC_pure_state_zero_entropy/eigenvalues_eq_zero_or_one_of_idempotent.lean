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
