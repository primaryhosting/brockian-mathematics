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

set_option autoImplicit false

namespace CS

open Nat.Partrec.Code

/-- The index set of a property `P` of partial functions: the set of natural numbers `n`
such that the partial function computed by the `n`-th program satisfies `P`.

This is a *semantic* (extensional) set by construction: membership of `n` depends only on the
partial function `eval (ofNat Code n)` computed by the program with index `n`, not on the
program itself. -/

theorem computablePred_indexSet_iff (P : (ℕ →. ℕ) → Prop) :
    ComputablePred (fun n : ℕ => n ∈ indexSet P) ↔
      ((∀ u : ℕ →. ℕ, Nat.Partrec u → P u) ∨ ∀ u : ℕ →. ℕ, Nat.Partrec u → ¬ P u) := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨g, hg, hgP⟩, ⟨f, hf, hfP⟩⟩ := hcon
    exact rice_extended P hf hg hfP hgP h
  · rintro (hall | hnone)
    · refine ComputablePred.computable_iff.2 ⟨fun _ => true, Computable.const _, ?_⟩
      funext n
      refine propext ⟨fun _ => rfl, fun _ => ?_⟩
      exact hall _ (exists_code.2 ⟨_, rfl⟩)
    · refine ComputablePred.computable_iff.2 ⟨fun _ => false, Computable.const _, ?_⟩
      funext n
      refine propext ⟨fun hn => ?_, fun hn => absurd hn (by simp)⟩
      exact absurd hn (hnone _ (exists_code.2 ⟨_, rfl⟩))

/-- An instance of `CS.rice_extended`: the set of indices of programs computing the nowhere-defined
partial function is not recursive. -/
