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

theorem canonical_commutation_satisfiable :
    ∃ (X P : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ)) (psi : ℕ →₀ ℂ),
      (∀ u v, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ) ∧ (∀ u v, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ) ∧
      ‖psi‖ = 1 ∧ X (P psi) - P (X psi) = ((Complex.I * ((1 : ℝ) : ℂ))) • psi := by
  refine ⟨posOp, momOp, vacuum, posOp_symmetric, momOp_symmetric, norm_vacuum, ?_⟩
  rw [posOp_momOp_commutator]
  norm_num

/-- In this concrete model (with `ℏ = 1`), the uncertainty principle applies to the vacuum
state and gives `Δx · Δp ≥ 1/2`. -/
