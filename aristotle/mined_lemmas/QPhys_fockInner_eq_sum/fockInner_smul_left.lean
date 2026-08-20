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

lemma fockInner_smul_left (f g : ℕ →₀ ℂ) (r : ℂ) :
    fockInner (r • f) g = conj r * fockInner f g := by
  simp only [fockInner_eq_sum _ g (le_refl g.support), Finsupp.smul_apply, smul_eq_mul, map_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

