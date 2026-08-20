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

lemma norm_vacuum : ‖vacuum‖ = 1 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) vacuum
  rw [inner_vacuum_self] at h
  have h' : ((‖vacuum‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h.symm
  have h'' : ‖vacuum‖ ^ 2 = 1 := by exact_mod_cast h'
  nlinarith [norm_nonneg vacuum, h'']

/-- The hypotheses of `QPhys.heisenberg_uncertainty` are satisfiable with `ℏ = 1`:
the algebraic Fock space carries symmetric position and momentum operators obeying the
canonical commutation relation at the (normalized) vacuum state. -/
