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

import Mathlib

/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`, computed in the
eigenbasis: `S(ρ) = ∑ i, -λ i * log (λ i)` where the `λ i` are the (real) eigenvalues of `ρ`.
This is the standard definition of the entropy of a density matrix. -/
noncomputable def vonNeumannEntropy {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : ℝ :=
  ∑ i, Real.negMulLog (hρ.eigenvalues i)

/-- The density matrix of the pure state given by a vector `ψ`, i.e. `|ψ⟩⟨ψ|`, whose entries are
`ψ i * conj (ψ j)`. -/
def pureStateMatrix (psi : n → ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => psi i * (starRingEnd ℂ) (psi j)

omit [Fintype n] [DecidableEq n] in
/-- A pure-state density matrix is Hermitian. -/
theorem pureStateMatrix_isHermitian (psi : n → ℂ) :
    (pureStateMatrix psi).IsHermitian := by
  ext i j
  simp [pureStateMatrix, Matrix.conjTranspose_apply, mul_comm]

omit [DecidableEq n] in
/-- For a unit vector `ψ`, the pure-state density matrix `|ψ⟩⟨ψ|` is idempotent
(it is an orthogonal projection onto the line spanned by `ψ`). -/
theorem pureStateMatrix_mul_self (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    pureStateMatrix psi * pureStateMatrix psi = pureStateMatrix psi := by
  have hsum : ∑ k, (starRingEnd ℂ) (psi k) * psi k = 1 := by
    have : ∀ k, (starRingEnd ℂ) (psi k) * psi k = ((‖psi k‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [mul_comm, Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq (psi k)
    simp only [this, ← Complex.ofReal_sum, hpsi, Complex.ofReal_one]
  ext i j
  simp only [pureStateMatrix, Matrix.mul_apply, Matrix.of_apply]
  calc ∑ k, psi i * (starRingEnd ℂ) (psi k) * (psi k * (starRingEnd ℂ) (psi j))
      = (∑ k, (starRingEnd ℂ) (psi k) * psi k) * (psi i * (starRingEnd ℂ) (psi j)) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = psi i * (starRingEnd ℂ) (psi j) := by rw [hsum, one_mul]

omit [DecidableEq n] in
/-- Sanity check: a pure-state density matrix built from a unit vector has trace `1`,
so it really is a density matrix. -/
theorem pureStateMatrix_trace (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    (pureStateMatrix psi).trace = 1 := by
  have : ∀ k, psi k * (starRingEnd ℂ) (psi k) = ((‖psi k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq (psi k)
  simp only [Matrix.trace, Matrix.diag_apply, pureStateMatrix, Matrix.of_apply, this,
    ← Complex.ofReal_sum, hpsi, Complex.ofReal_one]

/-- Every eigenvalue of a Hermitian idempotent matrix satisfies `λ² = λ`. -/
theorem eigenvalue_sq_eq_self_of_idempotent {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hidem : ρ * ρ = ρ) (j : n) : (hρ.eigenvalues j) ^ 2 = hρ.eigenvalues j := by
  set v := (hρ.eigenvectorBasis j).ofLp with hv
  have h1 : ρ *ᵥ v = hρ.eigenvalues j • v := hρ.mulVec_eigenvectorBasis j
  have h2 : (ρ * ρ) *ᵥ v = ρ *ᵥ (ρ *ᵥ v) := by rw [Matrix.mulVec_mulVec]
  rw [hidem, h1, Matrix.mulVec_smul, h1] at h2
  have hvne : v ≠ 0 := by
    have := (hρ.eigenvectorBasis).orthonormal.ne_zero j
    simpa [hv] using this
  have hz : ((hρ.eigenvalues j) ^ 2 - hρ.eigenvalues j) • v = 0 := by
    rw [sub_smul, sq, SemigroupAction.mul_smul, ← h2, sub_self]
  rcases smul_eq_zero.mp hz with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h hvne

/-- If `λ² = λ` then `-λ log λ = 0` (since `λ` is `0` or `1`). -/
theorem negMulLog_eq_zero_of_sq_eq_self {x : ℝ} (hx : x ^ 2 = x) :
    Real.negMulLog x = 0 := by
  have hcases : x = 0 ∨ x = 1 := by
    have h : x * (x - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hcases with h | h <;> simp [h, Real.negMulLog]

/-- **The von Neumann entropy of a pure state is zero.**
For a unit vector `ψ`, the density matrix `ρ = |ψ⟩⟨ψ|` satisfies `S(ρ) = -Tr(ρ log ρ) = 0`. -/
theorem pure_state_zero_entropy (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    vonNeumannEntropy (pureStateMatrix_isHermitian psi) = 0 := by
  unfold vonNeumannEntropy
  refine Finset.sum_eq_zero fun j _ => ?_
  exact negMulLog_eq_zero_of_sq_eq_self
    (eigenvalue_sq_eq_self_of_idempotent _ (pureStateMatrix_mul_self psi hpsi) j)

end QC

