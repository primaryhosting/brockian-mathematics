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

open Matrix BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`, computed
spectrally as `-∑ λᵢ log λᵢ` over the eigenvalues of `ρ`.  (Recall `Real.log 0 = 0`, so the
usual convention `0 log 0 = 0` is automatic.) -/
noncomputable def vonNeumannEntropy {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : ℝ :=
  -∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i)

/-- A density matrix is a *pure state* if it is the rank-one projector `|ψ⟩⟨ψ|` onto some
unit vector `ψ`. -/
def IsPureState (ρ : Matrix n n ℂ) : Prop :=
  ∃ ψ : n → ℂ, (∑ i, ‖ψ i‖ ^ 2) = 1 ∧ ρ = Matrix.vecMulVec ψ (star ψ)

omit [DecidableEq n] in
theorem IsPureState.isHermitian {ρ : Matrix n n ℂ} (h : IsPureState ρ) : ρ.IsHermitian := by
  obtain ⟨ψ, -, rfl⟩ := h
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]

omit [DecidableEq n] in
theorem IsPureState.isIdempotent {ρ : Matrix n n ℂ} (h : IsPureState ρ) : ρ * ρ = ρ := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  have hψ' : ∑ k, ψ k * (starRingEnd ℂ) (ψ k) = 1 := by
    have : ∀ k, ψ k * (starRingEnd ℂ) (ψ k) = ((‖ψ k‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [mul_comm, Complex.normSq_eq_conj_mul_self.symm]
      simp [Complex.normSq_eq_norm_sq]
    simp only [this]
    rw [← Complex.ofReal_sum, hψ, Complex.ofReal_one]
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def]
  calc ∑ k, ψ i * (starRingEnd ℂ) (ψ k) * (ψ k * (starRingEnd ℂ) (ψ j))
      = (∑ k, ψ k * (starRingEnd ℂ) (ψ k)) * (ψ i * (starRingEnd ℂ) (ψ j)) := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; ring
    _ = ψ i * (starRingEnd ℂ) (ψ j) := by rw [hψ', one_mul]

/-- The eigenvalues of a Hermitian idempotent matrix are `0` or `1`. -/
theorem eigenvalues_eq_zero_or_one {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hidem : ρ * ρ = ρ) (i : n) : hρ.eigenvalues i = 0 ∨ hρ.eigenvalues i = 1 := by
  set v : n → ℂ := ⇑(hρ.eigenvectorBasis i) with hv
  set l : ℝ := hρ.eigenvalues i with hl
  have hmul : ρ *ᵥ v = l • v := hρ.mulVec_eigenvectorBasis i
  have h2 : (l * l) • v = l • v := by
    have : ρ *ᵥ (ρ *ᵥ v) = ρ *ᵥ v := by
      rw [Matrix.mulVec_mulVec, hidem]
    rw [hmul] at this
    rw [Matrix.mulVec_smul, hmul] at this
    rw [SemigroupAction.mul_smul]
    exact this
  have hvne : v ≠ 0 := by
    intro hzero
    have : ‖hρ.eigenvectorBasis i‖ = 1 := hρ.eigenvectorBasis.orthonormal.1 i
    rw [show (hρ.eigenvectorBasis i) = 0 from by
      ext k; exact congrFun hzero k] at this
    simp at this
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hvne (funext hcon)
  have hck := congrFun h2 k
  simp only [Pi.smul_apply, Complex.real_smul] at hck
  have hll : ((l * l : ℝ) : ℂ) = ((l : ℝ) : ℂ) := mul_right_cancel₀ hk hck
  have hl2 : l * l = l := by exact_mod_cast hll
  have : l * (l - 1) = 0 := by ring_nf; linarith [hl2]
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- **Pure states have zero von Neumann entropy**: if `ρ = |ψ⟩⟨ψ|` for a unit vector `ψ`,
then `S(ρ) = -Tr(ρ log ρ) = 0`. -/
theorem pure_state_zero_entropy {ρ : Matrix n n ℂ} (h : IsPureState ρ) :
    vonNeumannEntropy h.isHermitian = 0 := by
  have hidem := h.isIdempotent
  unfold vonNeumannEntropy
  rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro i _
  rcases eigenvalues_eq_zero_or_one h.isHermitian hidem i with hi | hi <;> simp [hi]

/-- Sanity check: pure states exist (e.g. `|0⟩⟨0|` on a qubit). -/
example : IsPureState (Matrix.vecMulVec ![(1 : ℂ), 0] (star ![(1 : ℂ), 0])) :=
  ⟨![1, 0], by simp [Fin.sum_univ_two], rfl⟩

end QC

