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

lemma numberOp_eigen_nat {lam : ℂ} {v : V} (hv0 : v ≠ 0) (hv : numberOp a ad v = lam • v) :
    ∃ n : ℕ, lam = (n : ℂ) := by
  suffices H : ∀ N : ℕ, ∀ (mu : ℂ) (w : V), w ≠ 0 → numberOp a ad w = mu • w →
      mu.re ≤ (N : ℝ) → ∃ n : ℕ, mu = (n : ℂ) by
    exact H ⌈lam.re⌉₊ lam v hv0 hv (Nat.le_ceil _)
  intro N
  induction N with
  | zero =>
    intro mu w hw hev hle
    obtain ⟨him, hre⟩ := eigen_nonneg_real a ad hadj hw hev
    refine ⟨0, ?_⟩
    have hre0 : mu.re = 0 := le_antisymm (by simpa using hle) hre
    apply Complex.ext <;> simp [him, hre0]
  | succ N ih =>
    intro mu w hw hev hle
    obtain ⟨him, hre⟩ := eigen_nonneg_real a ad hadj hw hev
    by_cases hmu : mu = 0
    · exact ⟨0, by simp [hmu]⟩
    · have haw : a w ≠ 0 := a_ne_zero_of_eigen_ne_zero a ad hadj hw hev hmu
      have hlow := numberOp_lower a ad hcomm hev
      have hle' : (mu - 1).re ≤ (N : ℝ) := by
        simp only [Complex.sub_re, Complex.one_re]
        push_cast at hle
        linarith
      obtain ⟨m, hm⟩ := ih (mu - 1) (a w) haw hlow hle'
      exact ⟨m + 1, by push_cast; linear_combination hm⟩

include hadj hcomm in
/-- Starting from a vacuum vector, every natural number is an eigenvalue. -/
