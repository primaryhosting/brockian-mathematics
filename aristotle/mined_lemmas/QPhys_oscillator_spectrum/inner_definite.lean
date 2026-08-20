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

lemma inner_definite (f : FockSpace) (h : ⟪f, f⟫_ℂ = 0) : f = 0 := by
  rw [inner_self_eq, Complex.ofReal_eq_zero] at h
  have hz : ∀ i ∈ f.support, Complex.normSq (f i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).mp h
  ext i
  by_cases hi : i ∈ f.support
  · simpa using Complex.normSq_eq_zero.mp (hz i hi)
  · simpa using Finsupp.notMem_support_iff.mp hi

