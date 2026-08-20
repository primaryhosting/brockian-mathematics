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
open ComplexConjugate

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Heisenberg uncertainty principle.**

Let `X` and `P` be (everywhere-defined) linear operators on a complex inner product space
which are symmetric (`hX`, `hP`, i.e. they represent observables such as position and
momentum), and let `psi` be a normalized state on which the canonical commutation relation
`[X, P] psi = i ℏ psi` holds.  Writing
`Δx = ‖X psi - ⟪psi, X psi⟫ • psi‖` and `Δp = ‖P psi - ⟪psi, P psi⟫ • psi‖`
for the standard deviations of `X` and `P` in the state `psi`, one has `Δx · Δp ≥ ℏ / 2`.

The proof is the classical one: the commutator forces the imaginary part of
`⟪X psi - ⟪X⟫ psi, P psi - ⟪P⟫ psi⟫` to equal `ℏ / 2`, and the Cauchy–Schwarz inequality
(`norm_inner_le_norm` in Mathlib) bounds its modulus by `Δx · Δp`. -/
theorem heisenberg_uncertainty
    (X P : H →ₗ[ℂ] H) (hbar : ℝ) (psi : H) (hpsi : ‖psi‖ = 1)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hcomm : X (P psi) - P (X psi) = (Complex.I * hbar) • psi) :
    ‖X psi - (⟪psi, X psi⟫_ℂ) • psi‖ * ‖P psi - (⟪psi, P psi⟫_ℂ) • psi‖ ≥ hbar / 2 := by
  set a : ℂ := ⟪psi, X psi⟫_ℂ with ha_def
  set b : ℂ := ⟪psi, P psi⟫_ℂ with hb_def
  have hnorm : (⟪psi, psi⟫_ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  -- expectation values of symmetric operators are real
  have ha : conj a = a := by rw [ha_def, inner_conj_symm, hX]
  have hb : conj b = b := by rw [hb_def, inner_conj_symm, hP]
  have hxp : ⟪X psi, psi⟫_ℂ = a := by rw [hX]
  have hpp : ⟪P psi, psi⟫_ℂ = b := by rw [hP]
  set f : H := X psi - a • psi with hf
  set g : H := P psi - b • psi with hg
  -- the canonical commutation relation, in inner-product form
  have h1 : ⟪X psi, P psi⟫_ℂ - ⟪P psi, X psi⟫_ℂ = Complex.I * hbar := by
    rw [hX, hP, ← inner_sub_right, hcomm, inner_smul_right, hnorm, mul_one]
  -- shifting by the expectation values does not change the commutator
  have key : ⟪f, g⟫_ℂ - ⟪g, f⟫_ℂ = Complex.I * hbar := by
    simp only [hf, hg, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      ha, hb, hnorm, hxp, hpp]
    rw [← h1]
    ring
  -- hence the imaginary part of ⟪f, g⟫ is exactly ℏ / 2
  have him : (⟪f, g⟫_ℂ).im = hbar / 2 := by
    have h2 : ⟪g, f⟫_ℂ = conj ⟪f, g⟫_ℂ := (inner_conj_symm _ _).symm
    rw [h2] at key
    have h3 : (⟪f, g⟫_ℂ - conj ⟪f, g⟫_ℂ).im = (Complex.I * (hbar : ℂ)).im :=
      congrArg Complex.im key
    rw [Complex.sub_im, Complex.conj_im] at h3
    have h4 : (Complex.I * (hbar : ℂ)).im = hbar := by simp
    rw [h4] at h3
    linarith
  -- Cauchy–Schwarz finishes the proof
  have hcs : ‖⟪f, g⟫_ℂ‖ ≤ ‖f‖ * ‖g‖ := norm_inner_le_norm f g
  have him' : hbar / 2 ≤ ‖⟪f, g⟫_ℂ‖ := him ▸ Complex.im_le_norm _
  exact le_trans him' hcs

end QPhys

