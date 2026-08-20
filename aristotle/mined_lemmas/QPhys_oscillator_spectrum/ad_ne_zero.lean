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

lemma ad_ne_zero {lam : ℂ} {v : V} (hv0 : v ≠ 0) (hv : numberOp a ad v = lam • v) :
    ad v ≠ 0 := by
  obtain ⟨him, hre⟩ := eigen_nonneg_real a ad hadj hv0 hv
  have hraise := numberOp_raise a ad hcomm hv
  have hne : lam + 1 ≠ 0 := by
    intro h
    have : (lam + 1).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re] at this
    linarith
  intro hz
  -- if `ad v = 0` then the eigenvalue equation forces `(lam+1) • v = 0`
  have h2 : a (ad v) = (lam + 1) • v := by
    have h3 : a (ad v) = v + ad (a v) := sub_eq_iff_eq_add.mp (hcomm v)
    rw [numberOp_apply] at hv
    rw [h3, hv]
    module
  rw [hz] at h2
  simp only [map_zero] at h2
  have := (smul_eq_zero.mp h2.symm)
  rcases this with h3 | h3
  · exact hne h3
  · exact hv0 h3

include hadj hcomm in
/-- Every eigenvalue of the number operator is a natural number. -/
