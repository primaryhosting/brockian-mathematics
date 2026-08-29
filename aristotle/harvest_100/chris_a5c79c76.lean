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
-- (The required header is kept verbatim above; Lean forbids a module docstring `/-!`
-- before `import`, so it is written as an ordinary block comment.)

import Mathlib

open Matrix Finset

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The density matrix `ρ = |ψ⟩⟨ψ|` of the (column) vector `ψ`. -/
noncomputable def pureDensity (psi : n → ℂ) : Matrix n n ℂ :=
  Matrix.vecMulVec psi (fun i => starRingEnd ℂ (psi i))

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem pureDensity_apply (psi : n → ℂ) (i j : n) :
    pureDensity psi i j = psi i * starRingEnd ℂ (psi j) := rfl

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`.

Since `ρ` is Hermitian it is unitarily diagonalizable with real eigenvalues `λ i`,
and the functional calculus gives `-Tr(ρ log ρ) = ∑ i, -λ i * log (λ i)`, i.e. the
sum of `Real.negMulLog` over the spectrum (with the usual convention `0 log 0 = 0`,
which is exactly how `Real.negMulLog` is defined at `0`). -/
noncomputable def vonNeumannEntropy {rho : Matrix n n ℂ} (h : rho.IsHermitian) : ℝ :=
  ∑ i, Real.negMulLog (h.eigenvalues i)

omit [Fintype n] [DecidableEq n] in
/-- A pure-state density matrix is Hermitian. -/
theorem pureDensity_isHermitian (psi : n → ℂ) : (pureDensity psi).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, mul_comm]

omit [DecidableEq n] in
/-- A normalized pure state gives an idempotent density matrix (an orthogonal projection). -/
theorem pureDensity_mul_self (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    pureDensity psi * pureDensity psi = pureDensity psi := by
  have hsum : ∑ k, (starRingEnd ℂ) (psi k) * psi k = 1 := by
    have : ∀ k : n, (starRingEnd ℂ) (psi k) * psi k = ((‖psi k‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [mul_comm, Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq (psi k)
    simp only [this]
    rw [← Complex.ofReal_sum, hpsi, Complex.ofReal_one]
  ext i j
  simp only [Matrix.mul_apply, pureDensity_apply]
  calc ∑ k, psi i * (starRingEnd ℂ) (psi k) * (psi k * (starRingEnd ℂ) (psi j))
      = (∑ k, (starRingEnd ℂ) (psi k) * psi k) * (psi i * (starRingEnd ℂ) (psi j)) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = psi i * (starRingEnd ℂ) (psi j) := by rw [hsum, one_mul]

omit [DecidableEq n] in
/-- A normalized pure state gives a unit-trace density matrix. -/
theorem pureDensity_trace (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    (pureDensity psi).trace = 1 := by
  have : ∀ k : n, psi k * (starRingEnd ℂ) (psi k) = ((‖psi k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq (psi k)
  simp only [Matrix.trace, Matrix.diag_apply, pureDensity_apply, this]
  rw [← Complex.ofReal_sum, hpsi, Complex.ofReal_one]

/-- Every eigenvalue of a Hermitian idempotent matrix is `0` or `1`. -/
theorem eigenvalues_eq_zero_or_one {rho : Matrix n n ℂ} (h : rho.IsHermitian)
    (hidem : rho * rho = rho) (j : n) : h.eigenvalues j = 0 ∨ h.eigenvalues j = 1 := by
  set v : n → ℂ := (h.eigenvectorBasis j).ofLp with hv
  set r : ℝ := h.eigenvalues j with hr
  have hvne : v ≠ 0 := by
    have := (h.eigenvectorBasis).orthonormal.ne_zero j
    simpa [hv] using this
  have h1 : rho *ᵥ v = r • v := h.mulVec_eigenvectorBasis j
  have h2 : rho *ᵥ (rho *ᵥ v) = (r * r) • v := by
    rw [h1, Matrix.mulVec_smul, h1, smul_smul]
  have h3 : rho *ᵥ (rho *ᵥ v) = r • v := by
    rw [Matrix.mulVec_mulVec, hidem, h1]
  have hrr : (r * r) • v = r • v := by rw [← h2, h3]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hvne (funext hc)
  have := congrFun hrr i
  simp only [Pi.smul_apply, Complex.real_smul] at this
  have hcast : ((r * r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := mul_right_cancel₀ hi this
  have hreal : r * r = r := by exact_mod_cast hcast
  rcases mul_eq_zero.1 (show r * (r - 1) = 0 by nlinarith) with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by linarith)

/-- **Von Neumann entropy of a pure state is zero.**

If `ψ` is a normalized vector, the density matrix `ρ = |ψ⟩⟨ψ|` has
`S(ρ) = -Tr(ρ log ρ) = 0`. -/
theorem pure_state_zero_entropy (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    vonNeumannEntropy (pureDensity_isHermitian psi) = 0 := by
  unfold vonNeumannEntropy
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rcases eigenvalues_eq_zero_or_one (pureDensity_isHermitian psi)
      (pureDensity_mul_self psi hpsi) j with h | h <;>
    simp [h, Real.negMulLog]

end QC

