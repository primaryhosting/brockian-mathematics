/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Statement: Δx·Δp ≥ ℏ/2 for any normalized state (from the canonical commutator + Cauchy–Schwarz).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨T⟩_ψ = ⟪ψ, T ψ⟫` of an observable `T` in the state `ψ`. -/
noncomputable def expect (T : H →ₗ[ℂ] H) (psi : H) : ℂ := ⟪psi, T psi⟫_ℂ

/-- The standard deviation (uncertainty) `Δ T = ‖(T - ⟨T⟩) ψ‖` of an observable `T`
in the state `ψ`. -/
noncomputable def spread (T : H →ₗ[ℂ] H) (psi : H) : ℝ := ‖T psi - expect T psi • psi‖

/-- The expectation value of a symmetric operator is real. -/
lemma conj_expect (T : H →ₗ[ℂ] H) (psi : H)
    (hT : ∀ u v : H, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ) :
    conj (expect T psi) = expect T psi := by
  unfold expect
  rw [inner_conj_symm, hT]

/-- Expanding the inner product of the two centred vectors. -/
lemma inner_centred (X P : H →ₗ[ℂ] H) (psi : H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hnorm : ‖psi‖ = 1) :
    ⟪X psi - expect X psi • psi, P psi - expect P psi • psi⟫_ℂ
      = ⟪X psi, P psi⟫_ℂ - expect X psi * expect P psi := by
  have hself : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  have hxa : ⟪X psi, psi⟫_ℂ = expect X psi := by
    rw [hX]; rfl
  have hpb : ⟪psi, P psi⟫_ℂ = expect P psi := rfl
  have ha : conj (expect X psi) = expect X psi := conj_expect X psi hX
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, hself, hxa, hpb, ha]
  ring

/-- **Heisenberg uncertainty principle.**  If `X` and `P` are symmetric operators on a complex
inner product space satisfying the canonical commutation relation `[X, P] ψ = i ℏ ψ` at a
normalized state `ψ`, then the product of the uncertainties of `X` and `P` in the state `ψ`
is at least `ℏ / 2`. -/
theorem heisenberg_uncertainty
    (X P : H →ₗ[ℂ] H) (hbar : ℝ) (psi : H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hCCR : X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi)
    (hnorm : ‖psi‖ = 1) :
    spread X psi * spread P psi ≥ hbar / 2 := by
  set a : ℂ := expect X psi with ha_def
  set b : ℂ := expect P psi with hb_def
  set u : H := X psi - a • psi with hu_def
  set v : H := P psi - b • psi with hv_def
  set z : ℂ := ⟪u, v⟫_ℂ with hz_def
  have hself : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  -- the two expansions
  have h1 : z = ⟪X psi, P psi⟫_ℂ - a * b := inner_centred X P psi hX hnorm
  have h2 : ⟪v, u⟫_ℂ = ⟪P psi, X psi⟫_ℂ - b * a := inner_centred P X psi hP hnorm
  have h3 : ⟪v, u⟫_ℂ = conj z := by rw [hz_def, inner_conj_symm]
  -- the commutator computation
  have hcomm : ⟪X psi, P psi⟫_ℂ - ⟪P psi, X psi⟫_ℂ = Complex.I * (hbar : ℂ) := by
    have e1 : ⟪X psi, P psi⟫_ℂ = ⟪psi, X (P psi)⟫_ℂ := by rw [hX]
    have e2 : ⟪P psi, X psi⟫_ℂ = ⟪psi, P (X psi)⟫_ℂ := by rw [hP]
    rw [e1, e2, ← inner_sub_right, hCCR, inner_smul_right, hself, mul_one]
  have hzz : z - conj z = Complex.I * (hbar : ℂ) := by
    rw [← h3, h1, h2, ← hcomm]
    ring
  -- extract the imaginary part
  have him : z.im = hbar / 2 := by
    have := congrArg Complex.im hzz
    simp [Complex.sub_im, Complex.conj_im] at this
    linarith
  -- Cauchy-Schwarz
  have hcs : ‖z‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have hle : z.im ≤ ‖z‖ := le_trans (le_abs_self _) (Complex.abs_im_le_norm z)
  have : hbar / 2 ≤ ‖u‖ * ‖v‖ := by
    rw [← him]; exact le_trans hle hcs
  simpa [spread, hu_def, hv_def, ha_def, hb_def, ge_iff_le] using this

end QPhys

