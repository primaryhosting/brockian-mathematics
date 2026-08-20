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

lemma ccr (x : FockSpace) : annihilate (create x) - create (annihilate x) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, map_add, map_add, map_add,
      show annihilate (create f) + annihilate (create g)
          - (create (annihilate f) + create (annihilate g))
        = (annihilate (create f) - create (annihilate f))
          + (annihilate (create g) - create (annihilate g)) by abel, hf, hg]
  | single n c =>
    rw [create_single, annihilate_single, annihilate_single, create_single]
    have hsq : ((Real.sqrt (n + 1) : ℝ) : ℂ) * ((Real.sqrt (n + 1) : ℝ) : ℂ)
        = ((n : ℂ) + 1) := by
      have h : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 :=
        Real.mul_self_sqrt (by positivity)
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h
    match n with
    | 0 =>
      simp only [Nat.add_sub_cancel, Nat.zero_sub, Nat.cast_zero, Real.sqrt_zero,
        Complex.ofReal_zero, zero_mul]
      rw [← mul_assoc]
      norm_num at hsq ⊢
    | (m + 1) =>
      have hsqm : ((Real.sqrt (m + 1) : ℝ) : ℂ) * ((Real.sqrt (m + 1) : ℝ) : ℂ)
          = ((m : ℂ) + 1) := by
        have h : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 :=
          Real.mul_self_sqrt (by positivity)
        exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h
      simp only [Nat.add_sub_cancel]
      rw [← Finsupp.single_sub]
      congr 1
      push_cast at hsq hsqm ⊢
      rw [← mul_assoc, ← mul_assoc, hsq, hsqm]
      ring

/-- The vacuum vector. -/
