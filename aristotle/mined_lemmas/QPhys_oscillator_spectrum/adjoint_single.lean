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

lemma adjoint_single (m n : ℕ) (u v : ℂ) :
    ⟪annihilate (Finsupp.single m u), (Finsupp.single n v : FockSpace)⟫_ℂ
      = ⟪(Finsupp.single m u : FockSpace), create (Finsupp.single n v)⟫_ℂ := by
  rw [annihilate_single, create_single, inner_single_single, inner_single_single]
  by_cases h : m = n + 1
  · subst h
    simp [mul_comm, mul_assoc]
  · by_cases h2 : m - 1 = n
    · have hm0 : m = 0 := by omega
      subst hm0
      simp
    · simp [h, h2]

/-- `annihilate` and `create` are mutually adjoint. -/
