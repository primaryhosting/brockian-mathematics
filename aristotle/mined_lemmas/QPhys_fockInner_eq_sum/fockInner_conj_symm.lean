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

lemma fockInner_conj_symm (f g : ℕ →₀ ℂ) : conj (fockInner g f) = fockInner f g := by
  rw [fockInner_eq_sum g f (s := f.support ∪ g.support) Finset.subset_union_left,
      fockInner_eq_sum f g (s := f.support ∪ g.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [map_mul, Complex.conj_conj]
  ring_nf
  simp

