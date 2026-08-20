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

lemma fockInner_definite (f : ℕ →₀ ℂ) (h : fockInner f f = 0) : f = 0 := by
  have hre : ∑ n ∈ f.support, Complex.normSq (f n) * (n.factorial : ℝ) = 0 := by
    rw [← fockInner_self_re, h]; simp
  have hall : ∀ n ∈ f.support, Complex.normSq (f n) * (n.factorial : ℝ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun n _ =>
      mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))).mp hre
  ext n
  by_cases hn : n ∈ f.support
  · have h1 := hall n hn
    have hfact : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hns : Complex.normSq (f n) = 0 := by
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 hfact
    simpa using Complex.normSq_eq_zero.mp hns
  · simpa using (Finsupp.notMem_support_iff.mp hn)

/-- The Bargmann inner product core on the algebraic Fock space. -/
