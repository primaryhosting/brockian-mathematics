/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`.
We take the real part; for a symmetric operator `A` the inner product is already real. -/
noncomputable def expectation (A : H →ₗ[ℂ] H) (psi : H) : ℝ := (inner ℂ psi (A psi)).re

/-- The uncertainty (standard deviation) `Δ A = ‖(A - ⟨A⟩) ψ‖` of an observable `A`
in the state `ψ`.  For symmetric `A` and normalized `ψ` this equals
`√(⟨A²⟩ - ⟨A⟩²)`, since `‖(A - ⟨A⟩)ψ‖² = ⟪ψ, (A - ⟨A⟩)² ψ⟫`. -/
noncomputable def uncertainty (A : H →ₗ[ℂ] H) (psi : H) : ℝ :=
  ‖A psi - ((expectation A psi : ℝ) : ℂ) • psi‖

/-- **Heisenberg's uncertainty principle.**

Let `X` and `P` be symmetric (formally self-adjoint) operators on a complex inner product
space satisfying the canonical commutation relation `[X, P] = i ℏ` on all vectors, and let
`ψ` be a normalized state.  Then

  `Δx · Δp ≥ ℏ / 2`.

The proof is the classical one: writing `u = (X - ⟨X⟩)ψ`, `v = (P - ⟨P⟩)ψ`, the canonical
commutator gives `⟪u, v⟫ - ⟪v, u⟫ = i ℏ`, and the Cauchy–Schwarz inequality bounds the left
hand side in norm by `2 ‖u‖ ‖v‖ = 2 Δx Δp`. -/
theorem heisenberg_uncertainty
    (X P : H →ₗ[ℂ] H) (hbar : ℝ) (psi : H) (hpsi : ‖psi‖ = 1)
    (hX : ∀ u v : H, inner ℂ (X u) v = inner ℂ u (X v))
    (hP : ∀ u v : H, inner ℂ (P u) v = inner ℂ u (P v))
    (hcomm : ∀ u : H, X (P u) - P (X u) = (Complex.I * (hbar : ℂ)) • u) :
    uncertainty X psi * uncertainty P psi ≥ hbar / 2 := by
  set a : ℝ := expectation X psi with ha
  set b : ℝ := expectation P psi with hb
  set u : H := X psi - (a : ℂ) • psi with hu
  set v : H := P psi - (b : ℂ) • psi with hv
  have hps : (inner ℂ psi psi : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  -- The commutator identity, transported to the shifted vectors `u` and `v`.
  have key : (inner ℂ u v : ℂ) - inner ℂ v u = Complex.I * (hbar : ℂ) := by
    have e1 : (inner ℂ u v : ℂ) - inner ℂ v u = inner ℂ psi (X (P psi) - P (X psi)) := by
      simp only [hu, hv, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_ofReal, hX, hP, hps]
      ring
    rw [e1]
    simp [hcomm, hpsi]
  -- Cauchy–Schwarz.
  have hle : ‖Complex.I * (hbar : ℂ)‖ ≤ 2 * (‖u‖ * ‖v‖) := by
    rw [← key]
    calc ‖(inner ℂ u v : ℂ) - inner ℂ v u‖ ≤ ‖(inner ℂ u v : ℂ)‖ + ‖(inner ℂ v u : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ ‖u‖ * ‖v‖ + ‖v‖ * ‖u‖ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ = 2 * (‖u‖ * ‖v‖) := by ring
  have hnorm : ‖Complex.I * (hbar : ℂ)‖ = |hbar| := by simp [Complex.norm_I]
  rw [hnorm] at hle
  have hfin : hbar ≤ 2 * (uncertainty X psi * uncertainty P psi) :=
    calc hbar ≤ |hbar| := le_abs_self _
      _ ≤ 2 * (‖u‖ * ‖v‖) := hle
      _ = 2 * (uncertainty X psi * uncertainty P psi) := by rw [uncertainty, uncertainty]
  linarith

end QPhys

