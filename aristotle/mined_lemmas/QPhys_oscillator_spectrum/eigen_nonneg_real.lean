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

lemma eigen_nonneg_real {lam : ℂ} {v : V} (hv0 : v ≠ 0) (hv : numberOp a ad v = lam • v) :
    lam.im = 0 ∧ 0 ≤ lam.re := by
  have h := eigen_norm_eq a ad hadj hv
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have hnc : ((‖v‖ : ℂ)) ^ 2 ≠ 0 := by
    simpa [Complex.ofReal_eq_zero] using pow_ne_zero 2 (by exact_mod_cast hn : (‖v‖ : ℂ) ≠ 0)
  have hlam : lam = ((‖a v‖ ^ 2 / ‖v‖ ^ 2 : ℝ) : ℂ) := by
    have h2 := eq_div_of_mul_eq hnc h
    rw [h2]
    push_cast
    ring
  rw [hlam]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  positivity

include hadj in
