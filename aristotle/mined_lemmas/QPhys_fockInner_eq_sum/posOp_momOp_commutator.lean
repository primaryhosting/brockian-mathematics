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

lemma posOp_momOp_commutator (f : ℕ →₀ ℂ) :
    posOp (momOp f) - momOp (posOp f) = Complex.I • f := by
  have hccr : annih (creat f) = creat (annih f) + f := by
    have := annih_creat_sub_creat_annih f
    linear_combination (norm := abel) this
  simp only [posOp, momOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    map_smul, map_sub, map_add, hccr]
  module

/-- The vacuum state `e₀`. -/
