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

theorem inner_centered (X P : E →ₗ[ℂ] E)
    (hX : ∀ u v : E, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (psi : E) (hnorm : ‖psi‖ = 1) :
    ⟪X psi - ⟪psi, X psi⟫_ℂ • psi, P psi - ⟪psi, P psi⟫_ℂ • psi⟫_ℂ
      = ⟪psi, X (P psi)⟫_ℂ - ⟪psi, X psi⟫_ℂ * ⟪psi, P psi⟫_ℂ := by
  have hpp : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]; norm_num
  have ha : (starRingEnd ℂ) ⟪psi, X psi⟫_ℂ = ⟪psi, X psi⟫_ℂ :=
    conj_inner_self_of_symmetric X hX psi
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hpp, ha, hX psi (P psi)]
  rw [hX psi psi]
  ring

/-- The commutator relation forces the imaginary part of the inner product of the two
centred vectors to be `ℏ / 2`. -/
