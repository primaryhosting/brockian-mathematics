/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The index set of a semantic property `P` of partial functions: the set of natural
numbers `n` such that the partial recursive function computed by the `n`-th code
satisfies `P`. -/

theorem rice_extended_iff (P : (ℕ →. ℕ) → Prop) :
    (ComputablePred fun n : ℕ => n ∈ indexSet P) ↔
      ((∀ f : ℕ →. ℕ, Nat.Partrec f → P f) ∨ (∀ f : ℕ →. ℕ, Nat.Partrec f → ¬ P f)) := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    obtain ⟨g, hg, hgP⟩ := h1
    obtain ⟨f, hf, hfP⟩ := h2
    exact rice_extended P hf hg hfP hgP h
  · rintro (h | h)
    · have hall : ∀ n : ℕ, n ∈ indexSet P := fun n => h _ (partrec_eval _)
      exact ⟨fun n => Decidable.isTrue (hall n),
        (Computable.const true).of_eq fun n => by simp [hall n]⟩
    · have hnone : ∀ n : ℕ, n ∉ indexSet P := fun n => h _ (partrec_eval _)
      exact ⟨fun n => Decidable.isFalse (hnone n),
        (Computable.const false).of_eq fun n => by simp [hnone n]⟩

/-- An application, witnessing that the hypotheses of `rice_extended` are satisfiable: for each
input `n`, the set of indices of programs that halt on `n` is not recursive. -/
