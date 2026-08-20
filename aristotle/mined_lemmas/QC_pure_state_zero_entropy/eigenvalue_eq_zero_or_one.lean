/-
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- repeated verbatim as a module docstring immediately after the import.)

import Mathlib

/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open Matrix

set_option maxHeartbeats 1000000

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`, computed via its
(real) eigenvalues: `S(ρ) = -∑ λᵢ log λᵢ`.  (Recall `Real.log 0 = 0`, so the usual convention
`0 log 0 = 0` is automatic.) -/

theorem eigenvalue_eq_zero_or_one {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hidem : ρ * ρ = ρ)
    (i : n) : hρ.eigenvalues i = 0 ∨ hρ.eigenvalues i = 1 := by
  set lam : ℝ := hρ.eigenvalues i with hlam
  set v : n → ℂ := ⇑(hρ.eigenvectorBasis i) with hv
  have hmul : ρ *ᵥ v = lam • v := hρ.mulVec_eigenvectorBasis i
  have h1 : (ρ * ρ) *ᵥ v = (lam * lam) • v := by
    rw [← Matrix.mulVec_mulVec, hmul, Matrix.mulVec_smul, hmul, smul_smul]
  rw [hidem, hmul] at h1
  -- `v` is nonzero, so `lam * lam = lam`
  have hvne : v ≠ 0 := by
    intro h0
    have : ‖hρ.eigenvectorBasis i‖ = 1 := hρ.eigenvectorBasis.orthonormal.1 i
    rw [show (hρ.eigenvectorBasis i) = 0 from by
      ext k; simpa using congrFun h0 k] at this
    simp at this
  obtain ⟨k, hk⟩ : ∃ k : n, v k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hvne (funext hc)
  have hcoord := congrFun h1 k
  simp only [Pi.smul_apply, Complex.real_smul] at hcoord
  have h2 : (lam : ℂ) = ((lam * lam : ℝ) : ℂ) := mul_right_cancel₀ hk hcoord
  have hreal : lam = lam * lam := by exact_mod_cast h2
  rcases mul_eq_zero.mp (show lam * (lam - 1) = 0 by nlinarith) with h | h
  · exact Or.inl h
  · right; linarith

/-- **The von Neumann entropy of a pure state is zero.** -/
