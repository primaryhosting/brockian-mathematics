import Mathlib
import RequestProject.Main

/-!
# A concrete model for the canonical commutation relation

This file shows that the hypotheses of `QPhys.heisenberg_uncertainty` are *consistent* with a
nonzero `ℏ`: we build the (algebraic) Fock space of finitely supported sequences `ℕ →₀ ℂ`
with the Bargmann inner product `⟪eₘ, eₙ⟫ = n! δₘₙ`, the annihilation and creation operators,
and the resulting position and momentum operators `X`, `P`, which are symmetric and satisfy
`X P - P X = i` (i.e. `ℏ = 1`).
-/

open scoped ComplexConjugate InnerProductSpace
open Finsupp

namespace QPhys

/-! ## The Bargmann inner product on `ℕ →₀ ℂ` -/

/-- The Bargmann inner product: `⟪f, g⟫ = ∑ₙ conj (f n) * g n * n!`. -/

theorem heisenberg_uncertainty (X P : E →ₗ[ℂ] E)
    (hX : ∀ u v : E, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : E, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hbar : ℝ) (psi : E) (hnorm : ‖psi‖ = 1)
    (hcomm : X (P psi) - P (X psi) = ((Complex.I * hbar) : ℂ) • psi) :
    ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖ * ‖P psi - ⟪psi, P psi⟫_ℂ • psi‖ ≥ hbar / 2 := by
  set u : E := X psi - ⟪psi, X psi⟫_ℂ • psi
  set v : E := P psi - ⟪psi, P psi⟫_ℂ • psi
  have him : (⟪u, v⟫_ℂ).im = hbar / 2 := im_inner_centered X P hX hP hbar psi hnorm hcomm
  have hcs : ‖(⟪u, v⟫_ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have hle : (⟪u, v⟫_ℂ).im ≤ ‖(⟪u, v⟫_ℂ)‖ := Complex.im_le_norm _
  rw [ge_iff_le, ← him]
  exact hle.trans hcs

end Uncertainty

end QPhys

#print axioms QPhys.heisenberg_uncertainty

