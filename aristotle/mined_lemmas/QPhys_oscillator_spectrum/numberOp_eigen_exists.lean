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

lemma numberOp_eigen_exists (v0 : V) (hv0 : v0 ≠ 0) (hav0 : a v0 = 0) (n : ℕ) :
    ∃ v : V, v ≠ 0 ∧ numberOp a ad v = (n : ℂ) • v := by
  induction n with
  | zero => exact ⟨v0, hv0, by simp [numberOp_apply, hav0]⟩
  | succ n ih =>
    obtain ⟨v, hvne, hev⟩ := ih
    refine ⟨ad v, ad_ne_zero a ad hadj hcomm hvne hev, ?_⟩
    rw [numberOp_raise a ad hcomm hev]
    congr 1
    push_cast
    ring

end Ladder

/-- **Spectrum of the quantum harmonic oscillator.**
If `a`, `a†` are ladder operators on a complex inner product space (mutually adjoint, with
canonical commutation relation `[a, a†] = 1`), admitting a nonzero vacuum vector `v₀`
annihilated by `a`, then the point spectrum of the Hamiltonian
`H = ℏω (a†a + ½)` is exactly `{ℏω(n + ½) : n ∈ ℕ}`. -/
