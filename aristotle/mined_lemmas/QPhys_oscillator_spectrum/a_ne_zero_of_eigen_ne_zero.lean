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

lemma a_ne_zero_of_eigen_ne_zero {lam : ℂ} {v : V} (hv0 : v ≠ 0)
    (hv : numberOp a ad v = lam • v) (hlam : lam ≠ 0) : a v ≠ 0 := by
  intro hz
  have h := eigen_norm_eq a ad hadj hv
  rw [hz] at h
  simp only [norm_zero, Complex.ofReal_zero] at h
  rcases (by simpa using h : lam = 0 ∨ v = 0) with h1 | h1
  · exact hlam h1
  · exact hv0 h1

include hcomm in
/-- Lowering: `a v` is an eigenvector with eigenvalue `lam - 1`. -/
