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

theorem rice_codes {P : (ℕ →. ℕ) → Prop} (h : ComputablePred fun c : Code => P (eval c))
    {f g : ℕ →. ℕ} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hfP : P f) : P g := by
  obtain ⟨_, h⟩ := h
  obtain ⟨c, e⟩ :=
    fixed_point₂
      (Partrec.cond (h.comp Computable.fst)
        ((Partrec.nat_iff.2 hg).comp Computable.snd).to₂
        ((Partrec.nat_iff.2 hf).comp Computable.snd).to₂).to₂
  simp only [Bool.cond_decide] at e
  by_cases H : P (eval c)
  · simp only [H, if_true] at e
    show P fun b => g b
    rwa [← e]
  · simp only [H, if_false] at e
    rw [e] at H
    exact absurd hfP H

/-- **Rice's theorem (extended form).** If `P` is a property of partial functions which is
nontrivial on the partial recursive functions — i.e. some partial recursive function `f`
satisfies `P` and some partial recursive function `g` does not — then the index set of `P`
is not recursive (not decidable). -/
