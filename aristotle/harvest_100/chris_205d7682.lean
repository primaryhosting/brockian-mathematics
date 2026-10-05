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

/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Matrix

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`, computed in the
eigenbasis: if `ρ = U diag(λ) U*` then `-Tr(ρ log ρ) = -∑ λ i * log (λ i)`, i.e. the sum of
`Real.negMulLog` over the eigenvalues. -/
noncomputable def vonNeumannEntropy {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : ℝ :=
  ∑ i, Real.negMulLog (hρ.eigenvalues i)

/-- A density matrix is a *pure state* if it is of the form `|ψ⟩⟨ψ|` for a unit vector `ψ`. -/
def IsPureState (ρ : Matrix n n ℂ) : Prop :=
  ∃ ψ : n → ℂ, (∑ i, ‖ψ i‖ ^ 2) = 1 ∧ ρ = Matrix.vecMulVec ψ (star ψ)

omit [DecidableEq n] in
/-- A pure state `|ψ⟩⟨ψ|` is Hermitian. -/
theorem IsPureState.isHermitian {ρ : Matrix n n ℂ} (h : IsPureState ρ) : ρ.IsHermitian := by
  obtain ⟨ψ, -, rfl⟩ := h
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

omit [DecidableEq n] in
/-- A pure state `|ψ⟩⟨ψ|` is idempotent (it is a rank-one orthogonal projection). -/
theorem IsPureState.idempotent {ρ : Matrix n n ℂ} (h : IsPureState ρ) : ρ * ρ = ρ := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  have hsum : ∑ j, (starRingEnd ℂ) (ψ j) * ψ j = 1 := by
    have : ∀ j, (starRingEnd ℂ) (ψ j) * ψ j = ((‖ψ j‖ ^ 2 : ℝ) : ℂ) := by
      intro j
      rw [mul_comm, Complex.mul_conj]
      norm_cast
      simp [Complex.normSq_eq_norm_sq]
    rw [Finset.sum_congr rfl fun j _ => this j, ← Complex.ofReal_sum, hψ,
      Complex.ofReal_one]
  ext i k
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def]
  calc ∑ j, ψ i * (starRingEnd ℂ) (ψ j) * (ψ j * (starRingEnd ℂ) (ψ k))
      = (ψ i * (starRingEnd ℂ) (ψ k)) * ∑ j, (starRingEnd ℂ) (ψ j) * ψ j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ = ψ i * (starRingEnd ℂ) (ψ k) := by rw [hsum, mul_one]

/-- The matrix logarithm of a Hermitian matrix `ρ`: if `ρ = U diag(λ) U*` then
`log ρ = U diag(log λ) U*`. -/
noncomputable def matrixLog {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : Matrix n n ℂ :=
  (hρ.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((Real.log (hρ.eigenvalues i) : ℝ) : ℂ)) *
    star (hρ.eigenvectorUnitary : Matrix n n ℂ)

/-- The eigenvalue formula for the entropy really does compute `-Tr(ρ log ρ)`. -/
theorem vonNeumannEntropy_eq_neg_trace {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy hρ = -(ρ * matrixLog hρ).trace.re := by
  set U : Matrix n n ℂ := (hρ.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := by
    simp [hU, Matrix.mem_unitaryGroup_iff'.mp hρ.eigenvectorUnitary.2]
  have hspec : ρ = U * Matrix.diagonal (fun i => ((hρ.eigenvalues i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hρ.spectral_theorem]
    simp [hU, Unitary.conjStarAlgAut_apply, Function.comp_def]
  have hprod : ρ * matrixLog hρ =
      U * Matrix.diagonal
        (fun i => ((hρ.eigenvalues i : ℝ) : ℂ) * ((Real.log (hρ.eigenvalues i) : ℝ) : ℂ)) *
      star U := by
    have h := congrArg (fun M => M * matrixLog hρ) hspec
    simp only at h
    rw [h, matrixLog, ← hU, ← Matrix.diagonal_mul_diagonal]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
  have htrace : (ρ * matrixLog hρ).trace
      = ∑ i, ((hρ.eigenvalues i : ℝ) : ℂ) * ((Real.log (hρ.eigenvalues i) : ℝ) : ℂ) := by
    rw [hprod, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, Matrix.trace_diagonal]
  have hcast : (∑ i, ((hρ.eigenvalues i : ℝ) : ℂ) * ((Real.log (hρ.eigenvalues i) : ℝ) : ℂ))
      = ((∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [htrace, hcast, Complex.ofReal_re, vonNeumannEntropy, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.negMulLog]; ring

/-- Every eigenvalue of an idempotent Hermitian matrix is `0` or `1`. -/
theorem eigenvalues_eq_zero_or_one {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hidem : ρ * ρ = ρ) (i : n) : hρ.eigenvalues i = 0 ∨ hρ.eigenvalues i = 1 := by
  set μ : ℝ := hρ.eigenvalues i with hμ
  set v : n → ℂ := ⇑(hρ.eigenvectorBasis i) with hv
  have hmul : ρ *ᵥ v = μ • v := hρ.mulVec_eigenvectorBasis i
  have hv0 : v ≠ 0 := by
    have hnorm : ‖hρ.eigenvectorBasis i‖ = 1 := hρ.eigenvectorBasis.orthonormal.1 i
    intro hcon
    have : (hρ.eigenvectorBasis i : EuclideanSpace ℂ n) = 0 := by
      ext j
      exact congrFun hcon j
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have h1 : ρ *ᵥ (ρ *ᵥ v) = μ • (μ • v) := by
    rw [hmul, Matrix.mulVec_smul, hmul]
  have h2 : ρ *ᵥ (ρ *ᵥ v) = μ • v := by
    rw [Matrix.mulVec_mulVec, hidem, hmul]
  have h3 : (μ * μ) • v = μ • v := by
    rw [mul_smul, ← h1, h2]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
  have h4 : ((μ * μ : ℝ) : ℂ) * v j = (μ : ℂ) * v j := by
    have := congrFun h3 j
    simpa [Pi.smul_apply, Complex.real_smul] using this
  have h5 : (μ * μ : ℝ) = μ := by
    have := mul_right_cancel₀ hj h4
    exact_mod_cast this
  rcases mul_eq_zero.mp (by nlinarith : μ * (μ - 1) = 0) with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- **Pure states have zero von Neumann entropy.**
If `ρ = |ψ⟩⟨ψ|` for a unit vector `ψ`, then `S(ρ) = -Tr(ρ log ρ) = 0`. -/
theorem pure_state_zero_entropy {ρ : Matrix n n ℂ} (h : IsPureState ρ)
    (hρ : ρ.IsHermitian) : vonNeumannEntropy hρ = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases eigenvalues_eq_zero_or_one hρ h.idempotent i with hi | hi <;> rw [hi] <;> simp

omit [DecidableEq n] in
/-- A pure state is a density matrix: it has unit trace. -/
theorem IsPureState.trace_eq_one {ρ : Matrix n n ℂ} (h : IsPureState ρ) : ρ.trace = 1 := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  have : ∀ j, ψ j * (starRingEnd ℂ) (ψ j) = ((‖ψ j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [Complex.mul_conj]
    norm_cast
    simp [Complex.normSq_eq_norm_sq]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    RCLike.star_def]
  rw [Finset.sum_congr rfl fun j _ => this j, ← Complex.ofReal_sum, hψ, Complex.ofReal_one]

/-- Pure states exist: `|0⟩⟨0|` on a qubit is one, and its entropy is `0`. -/
example : IsPureState (Matrix.vecMulVec ![(1 : ℂ), 0] (star ![(1 : ℂ), 0])) :=
  ⟨![(1 : ℂ), 0], by norm_num [Fin.sum_univ_two], rfl⟩

end QC

