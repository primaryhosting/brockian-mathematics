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
def indexSet (P : (ℕ →. ℕ) → Prop) : Set ℕ :=
  {n : ℕ | P (eval (Denumerable.ofNat Nat.Partrec.Code n))}

/-- **Rice's theorem (extended form, on indices).**

If a semantic property `P` of partial functions is nontrivial — i.e. it holds of some partial
recursive function `f` and fails of some partial recursive function `g` — then its index set
`{n | P (eval (ofNat Code n))}` is not recursive (not a computable predicate on ℕ). -/
theorem rice_extended (P : (ℕ →. ℕ) → Prop) {f g : ℕ →. ℕ}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hfP : P f) (hgP : ¬ P g) :
    ¬ ComputablePred (fun n : ℕ => n ∈ indexSet P) := by
  intro h
  -- Transfer computability from indices to codes.
  have hcode : ComputablePred fun c : Nat.Partrec.Code => eval c ∈ {u : ℕ →. ℕ | P u} := by
    obtain ⟨b, hb, hpb⟩ := ComputablePred.computable_iff.1 h
    refine ComputablePred.computable_iff.2 ⟨fun c => b (Encodable.encode c), hb.comp
      Computable.encode, ?_⟩
    funext c
    have hc : (Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c)) = c :=
      Denumerable.ofNat_encode c
    have := congrFun hpb (Encodable.encode c)
    simp only [indexSet, Set.mem_setOf_eq, hc] at this
    simpa [Set.mem_setOf_eq] using this
  exact hgP (ComputablePred.rice {u : ℕ →. ℕ | P u} hcode hf hg hfP)

/-- **Rice's theorem, equivalent "trivial or non-recursive" form.**

The index set of a property `P` of partial functions is recursive if and only if `P` is trivial
on the partial recursive functions, i.e. it holds of all of them or of none of them. -/
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
theorem not_computablePred_indexSet_nowhereDefined :
    ¬ ComputablePred (fun n : ℕ => n ∈ indexSet fun u : ℕ →. ℕ => ∀ m, ¬ (u m).Dom) :=
  rice_extended _ Nat.Partrec.none Nat.Partrec.zero (fun _ h => h.elim)
    (fun h => h 0 trivial)

end CS

