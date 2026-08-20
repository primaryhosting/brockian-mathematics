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

lemma inner_creat_left (f g : ℕ →₀ ℂ) : ⟪creat f, g⟫_ℂ = ⟪f, annih g⟫_ℂ := by
  rw [← inner_conj_symm, ← inner_conj_symm f]
  exact congrArg conj (inner_annih_left g f).symm

/-- The canonical commutation relation `[annih, creat] = 1`. -/
