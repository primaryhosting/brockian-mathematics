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

open scoped BigOperators
open Matrix

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian (density) matrix `ρ`,
computed in the eigenbasis: `S(ρ) = ∑ i, -λ i * log (λ i)` where `λ` are the eigenvalues
of `ρ`. -/

theorem eigenvalues_eq_zero_or_one {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hidem : ρ * ρ = ρ) (i : n) : hρ.eigenvalues i = 0 ∨ hρ.eigenvalues i = 1 := by
  set v : n → ℂ := ⇑(hρ.eigenvectorBasis i) with hv
  have hmul : ρ *ᵥ v = (hρ.eigenvalues i : ℂ) • v := by
    have := hρ.mulVec_eigenvectorBasis i
    rw [hv]
    rw [this]
    ext j
    simp [Complex.real_smul]
  have hv0 : v ≠ 0 := by
    intro h
    have hnorm : ‖hρ.eigenvectorBasis i‖ = 1 := hρ.eigenvectorBasis.orthonormal.1 i
    have : (hρ.eigenvectorBasis i) = 0 := by
      ext j
      have := congrFun h j
      simpa using this
    rw [this] at hnorm
    simp at hnorm
  have h2 : ((hρ.eigenvalues i : ℂ)) ^ 2 • v = (hρ.eigenvalues i : ℂ) • v := by
    have : ρ *ᵥ (ρ *ᵥ v) = (ρ * ρ) *ᵥ v := by
      rw [Matrix.mulVec_mulVec]
    rw [hidem] at this
    calc ((hρ.eigenvalues i : ℂ)) ^ 2 • v
        = (hρ.eigenvalues i : ℂ) • ((hρ.eigenvalues i : ℂ) • v) := by
          rw [smul_smul, sq]
      _ = (hρ.eigenvalues i : ℂ) • (ρ *ᵥ v) := by rw [hmul]
      _ = ρ *ᵥ ((hρ.eigenvalues i : ℂ) • v) := by rw [Matrix.mulVec_smul]
      _ = ρ *ᵥ (ρ *ᵥ v) := by rw [hmul]
      _ = ρ *ᵥ v := this
      _ = (hρ.eigenvalues i : ℂ) • v := hmul
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv0 (funext hc)
  have := congrFun h2 j
  simp only [Pi.smul_apply, smul_eq_mul] at this
  have hsq : ((hρ.eigenvalues i : ℂ)) ^ 2 = (hρ.eigenvalues i : ℂ) :=
    mul_right_cancel₀ hj this
  have hreal : (hρ.eigenvalues i) ^ 2 = hρ.eigenvalues i := by exact_mod_cast hsq
  have : hρ.eigenvalues i * (hρ.eigenvalues i - 1) = 0 := by nlinarith [hreal]
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- **The von Neumann entropy of a pure state is zero.** -/
