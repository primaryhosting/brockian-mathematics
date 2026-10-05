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

theorem computablePred_code_of_indexSet {P : (ℕ →. ℕ) → Prop}
    (h : ComputablePred fun n : ℕ => n ∈ indexSet P) :
    ComputablePred fun c : Code => P (eval c) := by
  obtain ⟨inst, hcomp⟩ := h
  have key : ∀ c : Code, (Encodable.encode c ∈ indexSet P) ↔ P (eval c) := by
    intro c
    simp only [indexSet, Set.mem_setOf_eq, Denumerable.ofNat_encode]
  refine ⟨fun c => decidable_of_iff _ (key c), ?_⟩
  have hc := hcomp.comp (Computable.encode (α := Code))
  refine hc.of_eq fun c => ?_
  simp only [decide_eq_decide]
  exact key c

/-- **Core of Rice's theorem, on codes.** If the property `P` of partial functions is decidable
from a code, then `P` cannot separate two partial recursive functions: it holds of every
partial recursive function as soon as it holds of one. This is proved directly from Kleene's
second recursion theorem (`Nat.Partrec.Code.fixed_point₂`): given a decision procedure for `P`,
build a program that, on a code `c` for itself, computes `g` if `P (eval c)` holds and `f`
otherwise; a fixed point of this construction contradicts the decision procedure unless `P g`
holds. -/
