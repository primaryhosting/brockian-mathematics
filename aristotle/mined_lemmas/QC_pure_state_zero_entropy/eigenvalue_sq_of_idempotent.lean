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
