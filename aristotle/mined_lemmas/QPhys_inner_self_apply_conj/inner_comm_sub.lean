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

lemma inner_comm_sub (X P : H →ₗ[ℂ] H) (hbar : ℝ) (psi : H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hcomm : ∀ u : H, X (P u) - P (X u) = (Complex.I * hbar) • u)
    (hnorm : ‖psi‖ = 1) :
    ⟪X psi - ⟪psi, X psi⟫_ℂ • psi, P psi - ⟪psi, P psi⟫_ℂ • psi⟫_ℂ
      - ⟪P psi - ⟪psi, P psi⟫_ℂ • psi, X psi - ⟪psi, X psi⟫_ℂ • psi⟫_ℂ
      = Complex.I * hbar := by
  have hself : (⟪psi, psi⟫_ℂ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  have ha : conj ⟪psi, X psi⟫_ℂ = ⟪psi, X psi⟫_ℂ := inner_self_apply_conj X psi hX
  have hb : conj ⟪psi, P psi⟫_ℂ = ⟪psi, P psi⟫_ℂ := inner_self_apply_conj P psi hP
  have hXs : ⟪X psi, psi⟫_ℂ = ⟪psi, X psi⟫_ℂ := by rw [← inner_conj_symm, ha]
  have hPs : ⟪P psi, psi⟫_ℂ = ⟪psi, P psi⟫_ℂ := by rw [← inner_conj_symm, hb]
  have hkey : ⟪X psi, P psi⟫_ℂ - ⟪P psi, X psi⟫_ℂ = Complex.I * hbar := by
    have h1 : ⟪X psi, P psi⟫_ℂ = ⟪psi, X (P psi)⟫_ℂ := hX _ _
    have h2 : ⟪P psi, X psi⟫_ℂ = ⟪psi, P (X psi)⟫_ℂ := hP _ _
    rw [h1, h2, ← inner_sub_right, hcomm psi, inner_smul_right, hself, mul_one]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, ha, hb,
    hXs, hPs, hself]
  rw [← hkey]
  ring

