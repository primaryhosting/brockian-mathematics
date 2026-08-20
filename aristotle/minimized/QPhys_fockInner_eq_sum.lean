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

noncomputable def fockInner (f g : ℕ →₀ ℂ) : ℂ :=
  g.sum fun n c => conj (f n) * c * (n.factorial : ℂ)

lemma fockInner_eq_sum (f g : ℕ →₀ ℂ) {s : Finset ℕ} (hs : g.support ⊆ s) :
    fockInner f g = ∑ n ∈ s, conj (f n) * g n * (n.factorial : ℂ) := by
  refine Finsupp.sum_of_support_subset g hs _ ?_
  intro i _; ring
