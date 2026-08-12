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

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Functional calculus for a Hermitian matrix: `hermFun hρ f` is the matrix obtained by
applying the real function `f` to the eigenvalues of `ρ`, in an eigenbasis of `ρ`. -/
noncomputable def hermFun {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (f : ℝ → ℝ) : Matrix n n ℂ :=
  (hρ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((f (hρ.eigenvalues i) : ℝ) : ℂ)) *
    star (hρ.eigenvectorUnitary : Matrix n n ℂ)

/-- The matrix `ρ log ρ` (with the convention `0 * log 0 = 0`). -/
noncomputable def mulLog {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : Matrix n n ℂ :=
  hermFun hρ (fun x => x * Real.log x)

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`. -/
noncomputable def vonNeumannEntropy {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : ℝ :=
  -(mulLog hρ).trace.re

lemma trace_hermFun {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (f : ℝ → ℝ) :
    (hermFun hρ f).trace = ∑ i, ((f (hρ.eigenvalues i) : ℝ) : ℂ) := by
  rw [hermFun, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
    Matrix.trace_diagonal]

lemma vonNeumannEntropy_eq {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy hρ = -∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
  rw [vonNeumannEntropy, mulLog, trace_hermFun]
  norm_num

/-- Applying the identity function to the eigenvalues recovers the matrix itself
(spectral theorem). -/
lemma hermFun_id {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : hermFun hρ (fun x => x) = ρ := by
  conv_rhs => rw [hρ.spectral_theorem]
  simp [hermFun, Function.comp_def]

/-- The functional calculus is multiplicative. -/
lemma hermFun_mul {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (f g : ℝ → ℝ) :
    hermFun hρ f * hermFun hρ g = hermFun hρ (fun x => f x * g x) := by
  have hU : star (hρ.eigenvectorUnitary : Matrix n n ℂ) *
      (hρ.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self _
  simp only [hermFun]
  calc (hρ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((f (hρ.eigenvalues i) : ℝ) : ℂ))
        * star (hρ.eigenvectorUnitary : Matrix n n ℂ) *
        ((hρ.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (fun i => ((g (hρ.eigenvalues i) : ℝ) : ℂ)) *
          star (hρ.eigenvectorUnitary : Matrix n n ℂ))
      = (hρ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => ((f (hρ.eigenvalues i) : ℝ) : ℂ)) *
        (star (hρ.eigenvectorUnitary : Matrix n n ℂ) *
          (hρ.eigenvectorUnitary : Matrix n n ℂ)) *
        (diagonal (fun i => ((g (hρ.eigenvalues i) : ℝ) : ℂ)) *
          star (hρ.eigenvectorUnitary : Matrix n n ℂ)) := by
        simp only [mul_assoc]
    _ = (hρ.eigenvectorUnitary : Matrix n n ℂ) *
        (diagonal (fun i => ((f (hρ.eigenvalues i) : ℝ) : ℂ)) *
          diagonal (fun i => ((g (hρ.eigenvalues i) : ℝ) : ℂ))) *
        star (hρ.eigenvectorUnitary : Matrix n n ℂ) := by
        rw [hU, mul_one]; simp only [mul_assoc]
    _ = _ := by rw [Matrix.diagonal_mul_diagonal]; push_cast; ring_nf

/-- `mulLog hρ` really is the product of `ρ` with the matrix logarithm of `ρ`. -/
lemma mulLog_eq_mul_hermFun_log {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    mulLog hρ = ρ * hermFun hρ Real.log := by
  have h := hermFun_mul hρ (fun x => x) Real.log
  rw [hermFun_id] at h
  rw [mulLog]
  exact h.symm

/-- The entropy is `-Tr (ρ log ρ)` with `log ρ` the Hermitian functional calculus logarithm. -/
lemma vonNeumannEntropy_eq_neg_trace {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy hρ = -(ρ * hermFun hρ Real.log).trace.re := by
  rw [vonNeumannEntropy, mulLog_eq_mul_hermFun_log]

/-- The eigenvalues of a Hermitian idempotent matrix are `0` or `1`. -/
lemma eigenvalues_eq_zero_or_one {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hidem : ρ * ρ = ρ)
    (i : n) : hρ.eigenvalues i = 0 ∨ hρ.eigenvalues i = 1 := by
  set v : n → ℂ := ⇑(hρ.eigenvectorBasis i) with hv
  set μ : ℝ := hρ.eigenvalues i with hμ
  have h1 : ρ *ᵥ v = μ • v := hρ.mulVec_eigenvectorBasis i
  have h2 : (μ * μ) • v = μ • v := by
    have : ρ *ᵥ (ρ *ᵥ v) = μ • (μ • v) := by rw [h1, Matrix.mulVec_smul, h1]
    rw [Matrix.mulVec_mulVec, hidem, h1, smul_smul] at this
    exact this.symm
  have hvne : v ≠ 0 := by
    intro h
    have hb : hρ.eigenvectorBasis i = 0 := by
      ext j
      simpa using congrFun h j
    have := (hρ.eigenvectorBasis).orthonormal.1 i
    rw [hb] at this
    simp at this
  have hsq : μ * μ = μ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hvne
    have h3 := congrFun h2 j
    rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul, Complex.real_smul] at h3
    have h4 : ((μ * μ : ℝ) : ℂ) = ((μ : ℝ) : ℂ) := mul_right_cancel₀ hj h3
    exact_mod_cast h4
  have hfac : μ * (μ - 1) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- The density matrix `|ψ⟩⟨ψ|` of a pure state. -/
noncomputable def pureState (ψ : n → ℂ) : Matrix n n ℂ :=
  Matrix.vecMulVec ψ (star ψ)

omit [Fintype n] [DecidableEq n] in
lemma pureState_isHermitian (ψ : n → ℂ) : (pureState ψ).IsHermitian := by
  ext i j
  simp [pureState, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

omit [DecidableEq n] in
lemma pureState_idem (ψ : n → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    pureState ψ * pureState ψ = pureState ψ := by
  ext i j
  simp only [pureState, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    RCLike.star_def]
  have : ∑ k, ψ i * (starRingEnd ℂ) (ψ k) * (ψ k * (starRingEnd ℂ) (ψ j))
      = (ψ i * (starRingEnd ℂ) (ψ j)) * ∑ k, ((‖ψ k‖ : ℝ) : ℂ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (starRingEnd ℂ) (ψ k) * ψ k = ((‖ψ k‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.conj_mul']
    calc ψ i * (starRingEnd ℂ) (ψ k) * (ψ k * (starRingEnd ℂ) (ψ j))
        = (ψ i * (starRingEnd ℂ) (ψ j)) * ((starRingEnd ℂ) (ψ k) * ψ k) := by ring
      _ = (ψ i * (starRingEnd ℂ) (ψ j)) * ((‖ψ k‖ : ℝ) : ℂ) ^ 2 := by rw [hk]
  rw [this]
  have : ∑ k, ((‖ψ k‖ : ℝ) : ℂ) ^ 2 = 1 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hψ
    push_cast at this
    simpa using this
  rw [this, mul_one]

/-- **The von Neumann entropy of a pure state is zero.** -/
theorem pure_state_zero_entropy (ψ : n → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    vonNeumannEntropy (pureState_isHermitian ψ) = 0 := by
  rw [vonNeumannEntropy_eq]
  have : ∀ i : n, (pureState_isHermitian ψ).eigenvalues i *
      Real.log ((pureState_isHermitian ψ).eigenvalues i) = 0 := by
    intro i
    rcases eigenvalues_eq_zero_or_one (pureState_isHermitian ψ)
      (pureState_idem ψ hψ) i with h | h <;> simp [h]
  simp [this]

end QC

#print axioms QC.pure_state_zero_entropy

