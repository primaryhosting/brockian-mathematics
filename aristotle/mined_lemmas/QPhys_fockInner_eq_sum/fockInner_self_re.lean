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

lemma fockInner_self_re (f : ℕ →₀ ℂ) :
    (fockInner f f).re = ∑ n ∈ f.support, Complex.normSq (f n) * (n.factorial : ℝ) := by
  rw [fockInner_eq_sum f f (le_refl f.support), Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

