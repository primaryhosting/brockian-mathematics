/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module doc-comment `/-! ... -/`, so the
-- header above is written as a plain block comment and repeated as a docstring below.)

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩_ψ` of an operator `A` in the state `ψ`.
For a symmetric (observable) operator and a normalized state this is the physical
expectation value; we take the real part so that it is a real number by construction. -/
noncomputable def expect (A : H →ₗ[ℂ] H) (ψ : H) : ℝ := (⟪ψ, A ψ⟫_ℂ).re

/-- The standard deviation (uncertainty) `Δ A = ‖(A - ⟨A⟩) ψ‖` of an operator `A`
in the state `ψ`. -/
noncomputable def spread (A : H →ₗ[ℂ] H) (ψ : H) : ℝ :=
  ‖A ψ - (expect A ψ : ℂ) • ψ‖

/-- Expansion of the inner product of two centred vectors. -/
lemma inner_centered (A B : H →ₗ[ℂ] H) (ψ : H) (a b : ℝ)
    (hψ : ‖ψ‖ = 1) (hA : ∀ u v : H, ⟪A u, v⟫_ℂ = ⟪u, A v⟫_ℂ) :
    ⟪A ψ - (a : ℂ) • ψ, B ψ - (b : ℂ) • ψ⟫_ℂ
      = ⟪ψ, A (B ψ)⟫_ℂ - (b : ℂ) * ⟪ψ, A ψ⟫_ℂ - (a : ℂ) * ⟪ψ, B ψ⟫_ℂ
        + (a : ℂ) * (b : ℂ) := by
  have hnn : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hnn]
  rw [hA ψ (B ψ), hA ψ ψ]
  ring

/-- **Heisenberg uncertainty principle** (absolute-value form).
If `X` and `P` are symmetric operators on a complex inner product space satisfying the
canonical commutation relation `[X, P] ψ = i ℏ ψ` at a normalized state `ψ`, then
`Δx · Δp ≥ |ℏ| / 2`. -/
theorem heisenberg_uncertainty_abs (X P : H →ₗ[ℂ] H) (ψ : H) (hbar : ℝ)
    (hψ : ‖ψ‖ = 1)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hcomm : X (P ψ) - P (X ψ) = ((hbar : ℂ) * Complex.I) • ψ) :
    |hbar| / 2 ≤ spread X ψ * spread P ψ := by
  set a : ℝ := expect X ψ with ha
  set b : ℝ := expect P ψ with hb
  set u : H := X ψ - (a : ℂ) • ψ with hu
  set v : H := P ψ - (b : ℂ) • ψ with hv
  have hnn : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  -- the difference of the two inner products is the expectation of the commutator
  have key : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = (hbar : ℂ) * Complex.I := by
    rw [hu, hv, inner_centered X P ψ a b hψ hX, inner_centered P X ψ b a hψ hP]
    have : ⟪ψ, X (P ψ)⟫_ℂ - ⟪ψ, P (X ψ)⟫_ℂ = (hbar : ℂ) * Complex.I := by
      rw [← inner_sub_right, hcomm, inner_smul_right, hnn, mul_one]
    linear_combination this
  -- hence the imaginary part of ⟪u, v⟫ is ℏ/2
  have him : (⟪u, v⟫_ℂ).im = hbar / 2 := by
    have h2 : ⟪v, u⟫_ℂ = starRingEnd ℂ ⟪u, v⟫_ℂ := (inner_conj_symm v u).symm
    rw [h2] at key
    have := congrArg Complex.im key
    simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im] at this
    linarith
  calc |hbar| / 2 = |(⟪u, v⟫_ℂ).im| := by rw [him, abs_div]; norm_num
    _ ≤ ‖⟪u, v⟫_ℂ‖ := Complex.abs_im_le_norm _
    _ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
    _ = spread X ψ * spread P ψ := rfl

/-- **Heisenberg uncertainty principle**: `Δx · Δp ≥ ℏ / 2` for any normalized state `ψ`,
where `X`, `P` are symmetric (observable) operators obeying the canonical commutation
relation `[X, P] ψ = i ℏ ψ`.  The proof is the standard one: the commutator identity
plus the Cauchy–Schwarz inequality `‖⟪u, v⟫‖ ≤ ‖u‖ ‖v‖` (`norm_inner_le_norm`). -/
theorem heisenberg_uncertainty (X P : H →ₗ[ℂ] H) (ψ : H) (hbar : ℝ)
    (hψ : ‖ψ‖ = 1)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hcomm : X (P ψ) - P (X ψ) = ((hbar : ℂ) * Complex.I) • ψ) :
    hbar / 2 ≤ spread X ψ * spread P ψ := by
  have h := heisenberg_uncertainty_abs X P ψ hbar hψ hX hP hcomm
  have h2 := le_abs_self hbar
  linarith

end QPhys

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

