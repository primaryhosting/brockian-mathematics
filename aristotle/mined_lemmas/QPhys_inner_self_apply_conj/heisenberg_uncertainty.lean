/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped ComplexConjugate InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value of a symmetric operator in a state is real. -/

theorem heisenberg_uncertainty
    (X P : H →ₗ[ℂ] H) (hbar : ℝ) (psi : H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hcomm : ∀ u : H, X (P u) - P (X u) = (Complex.I * hbar) • u)
    (hnorm : ‖psi‖ = 1) :
    ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖ * ‖P psi - ⟪psi, P psi⟫_ℂ • psi‖ ≥ hbar / 2 := by
  set u : H := X psi - ⟪psi, X psi⟫_ℂ • psi with hu
  set v : H := P psi - ⟪psi, P psi⟫_ℂ • psi with hv
  have hid : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * hbar :=
    inner_comm_sub X P hbar psi hX hP hcomm hnorm
  have hconj : ⟪v, u⟫_ℂ = conj ⟪u, v⟫_ℂ := (inner_conj_symm _ _).symm
  have him : (⟪u, v⟫_ℂ).im = hbar / 2 := by
    have h2 := congrArg Complex.im hid
    rw [Complex.sub_im, hconj, Complex.conj_im] at h2
    simp [Complex.mul_im] at h2
    linarith
  calc hbar / 2 = (⟪u, v⟫_ℂ).im := him.symm
    _ ≤ ‖⟪u, v⟫_ℂ‖ := Complex.im_le_norm _
    _ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm _ _

/-- Sign-free form of the Heisenberg uncertainty relation: `Δx · Δp ≥ |ℏ| / 2`. -/
