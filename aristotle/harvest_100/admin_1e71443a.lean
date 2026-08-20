/-
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Classical

set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- **Rice's theorem.**  A property `P` of programs (encoded as `Nat.Partrec.Code`) which is
*semantic* (`hsem`: it depends only on the partial function the program computes) and
*nontrivial* (`hyes`: some program has it, `hno`: some program lacks it) is undecidable. -/
theorem rice_nontrivial (P : Nat.Partrec.Code → Prop)
    (hsem : ∀ c₁ c₂ : Nat.Partrec.Code, eval c₁ = eval c₂ → (P c₁ ↔ P c₂))
    (hyes : ∃ c, P c) (hno : ∃ c, ¬ P c) :
    ¬ ComputablePred P := by
  intro hcomp
  obtain ⟨cy, hcy⟩ := hyes
  obtain ⟨cn, hcn⟩ := hno
  -- `P` as a set of codes is semantic, hence by Rice's theorem it is `∅` or `univ`.
  have h := (ComputablePred.rice₂ {c | P c} (fun cf cg e => hsem cf cg e)).1
    (hcomp.of_eq (fun c => Iff.rfl))
  rcases h with h | h
  · have : cy ∈ ({c | P c} : Set Nat.Partrec.Code) := hcy
    rw [h] at this
    exact this
  · have : cn ∈ ({c | P c} : Set Nat.Partrec.Code) := h ▸ Set.mem_univ cn
    exact hcn this

/-- Function-level form of Rice's theorem: if a set `C` of partial functions contains the
partial function computed by some program and omits the one computed by some other program,
then `fun c => eval c ∈ C` is undecidable. -/
theorem rice_nontrivial_partrec (C : Set (ℕ →. ℕ))
    (hyes : ∃ cf : Nat.Partrec.Code, eval cf ∈ C)
    (hno : ∃ cg : Nat.Partrec.Code, eval cg ∉ C) :
    ¬ ComputablePred fun c : Nat.Partrec.Code => eval c ∈ C := by
  obtain ⟨cg, hcg⟩ := hno
  refine rice_nontrivial _ (fun c₁ c₂ e => by simp [e]) hyes ⟨cg, hcg⟩

end CS

