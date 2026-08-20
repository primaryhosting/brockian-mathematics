import RequestProject.Main

/-!
# A concrete model for the ladder-operator hypotheses

This file exhibits a concrete inner product space carrying ladder operators satisfying the
hypotheses of `QPhys.oscillator_spectrum`, so that the theorem is not vacuous.

The model is the algebraic Fock space of finitely supported complex sequences `ℕ →₀ ℂ`, with
`a (eₙ) = √n eₙ₋₁` and `a† (eₙ) = √(n+1) eₙ₊₁`.
-/

open scoped InnerProductSpace
open Finsupp

namespace QPhys

/-- The algebraic Fock space: finitely supported complex sequences. -/
abbrev FockSpace : Type := ℕ →₀ ℂ

namespace FockSpace

/-- The inner product on the algebraic Fock space. -/

lemma inner_self_eq (f : FockSpace) :
    ⟪f, f⟫_ℂ = ((∑ i ∈ f.support, Complex.normSq (f i) : ℝ) : ℂ) := by
  rw [inner_def]
  push_cast
  refine Finset.sum_congr (by simp) ?_
  intro i _
  rw [Complex.normSq_eq_conj_mul_self]

