/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
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

set_option grind.warning false

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The logarithm of a Hermitian matrix, defined through its spectral decomposition:
if `ρ = U D U*` with `D` the diagonal matrix of eigenvalues, then
`log ρ = U (log D) U*`. -/
noncomputable def hermLog {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) h.eigenvectorUnitary
    (Matrix.diagonal fun i => ((Real.log (h.eigenvalues i) : ℝ) : ℂ))

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`. -/
noncomputable def vonNeumannEntropy {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) : ℂ :=
  -(ρ * hermLog h).trace

/-- A density matrix is a *pure state* if it is of the form `|ψ⟩⟨ψ|` for a unit vector `ψ`. -/
def IsPureState (ρ : Matrix n n ℂ) : Prop :=
  ∃ ψ : n → ℂ, (∑ i, ‖ψ i‖ ^ 2) = 1 ∧ ρ = Matrix.of fun i j => ψ i * star (ψ j)

/-- A pure state is Hermitian. -/
theorem IsPureState.isHermitian {ρ : Matrix n n ℂ} (hp : IsPureState ρ) : ρ.IsHermitian := by
  obtain ⟨ψ, -, rfl⟩ := hp
  ext i j
  simp [Matrix.conjTranspose_apply, mul_comm]

/-- A pure state is an idempotent matrix (an orthogonal projection). -/
theorem IsPureState.mul_self {ρ : Matrix n n ℂ} (hp : IsPureState ρ) : ρ * ρ = ρ := by
  obtain ⟨ψ, hψ, rfl⟩ := hp
  have hψ' : ∑ k, star (ψ k) * ψ k = (1 : ℂ) := by
    have : ∀ k : n, star (ψ k) * ψ k = ((‖ψ k‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [Complex.star_def, Complex.conj_mul']
      norm_cast
    simp_rw [this, ← Complex.ofReal_sum, hψ, Complex.ofReal_one]
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  calc ∑ k, ψ i * star (ψ k) * (ψ k * star (ψ j))
      = (∑ k, star (ψ k) * ψ k) * (ψ i * star (ψ j)) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = ψ i * star (ψ j) := by rw [hψ', one_mul]

/-- Eigenvalues of an idempotent Hermitian matrix are `0` or `1`. -/
theorem eigenvalues_sq_eq_self {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) (hidem : ρ * ρ = ρ) (i : n) :
    h.eigenvalues i * h.eigenvalues i = h.eigenvalues i := by
  set v : n → ℂ := ⇑(h.eigenvectorBasis i) with hv
  set l : ℝ := h.eigenvalues i with hl
  have hmv : ρ *ᵥ v = l • v := h.mulVec_eigenvectorBasis i
  have hvne : v ≠ 0 := (WithLp.ofLp_eq_zero (p := 2)).ne.2 <|
    h.eigenvectorBasis.orthonormal.ne_zero i
  have h1 : ρ *ᵥ (ρ *ᵥ v) = (l * l) • v := by
    rw [hmv, Matrix.mulVec_smul, hmv, smul_smul]
  have h2 : ρ *ᵥ (ρ *ᵥ v) = l • v := by
    rw [Matrix.mulVec_mulVec, hidem, hmv]
  have h3 : (l * l) • v = l • v := by rw [← h1, h2]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hvne
  have h4 : ((l * l : ℝ) : ℂ) * v j = ((l : ℝ) : ℂ) * v j := by
    have := congrFun h3 j
    simpa [Pi.smul_apply, Complex.real_smul] using this
  have := mul_right_cancel₀ hj h4
  exact_mod_cast this

/-- The von Neumann entropy expressed via the eigenvalues: `S(ρ) = -∑ λᵢ log λᵢ`. -/
theorem vonNeumannEntropy_eq_sum {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) :
    vonNeumannEntropy h =
      -∑ i, ((h.eigenvalues i * Real.log (h.eigenvalues i) : ℝ) : ℂ) := by
  have hprod : ρ * hermLog h =
      Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) h.eigenvectorUnitary
        (Matrix.diagonal fun i => ((h.eigenvalues i * Real.log (h.eigenvalues i) : ℝ) : ℂ)) := by
    conv_lhs => rw [h.spectral_theorem]
    rw [hermLog, ← map_mul]
    congr 1
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    push_cast
    rfl
  rw [vonNeumannEntropy, hprod, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]

/-- **The von Neumann entropy of a pure state is zero.** -/
theorem pure_state_zero_entropy {ρ : Matrix n n ℂ} (hp : IsPureState ρ) :
    vonNeumannEntropy hp.isHermitian = 0 := by
  rw [vonNeumannEntropy_eq_sum]
  have hz : ∀ i : n, hp.isHermitian.eigenvalues i * Real.log (hp.isHermitian.eigenvalues i) = 0 := by
    intro i
    have h01 := eigenvalues_sq_eq_self hp.isHermitian hp.mul_self i
    set l := hp.isHermitian.eigenvalues i
    have : l = 0 ∨ l = 1 := by
      rcases eq_or_ne l 0 with h | h
      · exact Or.inl h
      · right
        field_simp at h01
        nlinarith [h01, sq_nonneg l]
    rcases this with h | h <;> simp [h]
  simp [hz]

end QC

