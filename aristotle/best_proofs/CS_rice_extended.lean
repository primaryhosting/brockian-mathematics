/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Statement: The set of indices of a nontrivial semantic property is not recursive (Rice).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Statement: The set of indices of a nontrivial semantic property is not recursive (Rice).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped Classical

set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code ComputablePred

/-- The index set of a property `P` of partial functions: the set of (codes of) programs
whose computed partial function has the property `P`. -/
def indexSet (P : Set (ℕ →. ℕ)) : Set Nat.Partrec.Code :=
  {c | Nat.Partrec.Code.eval c ∈ P}

/-- The index set of `P`, transported to natural-number indices via the standard
enumeration of codes. -/
def natIndexSet (P : Set (ℕ →. ℕ)) : Set ℕ :=
  {n | Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) ∈ P}

/-- A property of partial functions is *nontrivial* (as a semantic property of programs)
if some partial recursive function has it and some partial recursive function fails it. -/
def Nontrivial (P : Set (ℕ →. ℕ)) : Prop :=
  (∃ f, Nat.Partrec f ∧ f ∈ P) ∧ (∃ g, Nat.Partrec g ∧ g ∉ P)

/-- **Rice's theorem (extended form).**  If `P` is a nontrivial property of partial
functions — i.e. it is satisfied by some partial recursive function and refuted by some
other partial recursive function — then its index set `{c | eval c ∈ P}` is not
recursive.  Since membership only depends on the *function computed* by the code, this
covers every nontrivial semantic property of programs. -/
theorem rice_extended (P : Set (ℕ →. ℕ)) (hP : Nontrivial P) :
    ¬ ComputablePred (fun c : Nat.Partrec.Code => c ∈ indexSet P) := by
  rintro h
  obtain ⟨⟨f, hfp, hfP⟩, ⟨g, hgp, hgP⟩⟩ := hP
  exact hgP (ComputablePred.rice P h hfp hgp hfP)

/-- The same statement phrased for natural-number indices: the set of natural numbers
coding programs with a nontrivial semantic property is not recursive. -/
theorem rice_extended_nat (P : Set (ℕ →. ℕ)) (hP : Nontrivial P) :
    ¬ ComputablePred (fun n : ℕ => n ∈ natIndexSet P) := by
  intro h
  refine rice_extended P hP ?_
  have : ComputablePred fun c : Nat.Partrec.Code => (Encodable.encode c) ∈ natIndexSet P :=
    ComputablePred.computable_iff.2 <| by
      obtain ⟨_, hc⟩ := h
      exact ⟨_, hc.comp Computable.encode, by
        funext c; simp [natIndexSet]⟩
  refine this.of_eq fun c => ?_
  simp [natIndexSet, indexSet, Denumerable.ofNat_encode]

end CS

