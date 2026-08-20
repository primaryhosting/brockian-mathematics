/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace
open Matrix

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

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The spread (standard deviation) of the observable `A` in the state `psi`:
the norm of `A psi` after subtracting its mean value `⟪psi, A psi⟫ • psi`. -/

theorem heisenberg_uncertainty_abs
    {X P : H →ₗ[ℂ] H} (hX : IsSymmetricOp X) (hP : IsSymmetricOp P)
    {hbar : ℝ} {psi : H} (hpsi : ‖psi‖ = 1)
    (hcomm : X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi) :
    |hbar| / 2 ≤ spread X psi * spread P psi := by
  set a : ℂ := ⟪psi, X psi⟫_ℂ with ha_def
  set b : ℂ := ⟪psi, P psi⟫_ℂ with hb_def
  have hself : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  have hac : (starRingEnd ℂ) a = a := conj_expectation hX psi
  have hbc : (starRingEnd ℂ) b = b := conj_expectation hP psi
  set u : H := X psi - a • psi with hu
  set v : H := P psi - b • psi with hv
  -- the commutator gives the imaginary part of ⟪u, v⟫
  have hcm : ⟪X psi, P psi⟫_ℂ - ⟪P psi, X psi⟫_ℂ = Complex.I * hbar := by
    have h := congrArg (fun w => ⟪psi, w⟫_ℂ) hcomm
    simp only [inner_sub_right, inner_smul_right, hself, mul_one] at h
    rw [hX psi (P psi), hP psi (X psi)]
    exact h
  have huv : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * hbar := by
    have hXp : ⟪X psi, psi⟫_ℂ = a := by rw [ha_def, hX]
    have hPp : ⟪P psi, psi⟫_ℂ = b := by rw [hb_def, hP]
    simp only [hu, hv, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hself, hac, hbc, mul_one, hXp, hPp, ← ha_def, ← hb_def]
    rw [← hcm]; ring
  have hconj : ⟪v, u⟫_ℂ = (starRingEnd ℂ) (⟪u, v⟫_ℂ) := (inner_conj_symm v u).symm
  have him : (⟪u, v⟫_ℂ).im = hbar / 2 := by
    rw [hconj] at huv
    have h2 := congrArg Complex.im huv
    rw [Complex.sub_im, Complex.conj_im] at h2
    simp [Complex.mul_im] at h2
    linarith
  -- Cauchy-Schwarz
  calc |hbar| / 2 = |(⟪u, v⟫_ℂ).im| := by rw [him, abs_div]; norm_num
    _ ≤ ‖⟪u, v⟫_ℂ‖ := Complex.abs_im_le_norm _
    _ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm _ _
    _ = spread X psi * spread P psi := rfl

/-- **Heisenberg uncertainty principle**: `Δx · Δp ≥ ℏ / 2`.

For symmetric (formally self-adjoint) position and momentum operators `X`, `P` on a complex
inner product space and a normalized state `psi` obeying the canonical commutation relation
`[X, P] psi = i·ℏ·psi`, the product of the standard deviations of `X` and `P` in the state
`psi` is at least `ℏ / 2`. The proof combines the commutator identity with the
Cauchy–Schwarz inequality (`norm_inner_le_norm` in Mathlib). -/
