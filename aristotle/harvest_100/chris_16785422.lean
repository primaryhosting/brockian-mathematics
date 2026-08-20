import Mathlib

/-!
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

open Nat.Partrec Nat.Partrec.Code ComputablePred

/-- A property `P` of programs (codes) is *semantic* (extensional) when it depends only on the
partial function the program computes. -/
def Semantic (P : Code → Prop) : Prop :=
  ∀ cf cg : Code, eval cf = eval cg → (P cf ↔ P cg)

/-- A property `P` of programs is *nontrivial* when some program satisfies it and some
program does not. -/
def Nontrivial (P : Code → Prop) : Prop :=
  (∃ c : Code, P c) ∧ ∃ c : Code, ¬ P c

/-- **Rice's theorem.**  Every nontrivial semantic property of programs is undecidable. -/
theorem rice_nontrivial (P : Code → Prop) (hsem : Semantic P) (hnt : Nontrivial P) :
    ¬ ComputablePred P := by
  obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := hnt
  intro hP
  -- View `P` as a set of codes and apply Mathlib's `rice₂`.
  have h : ComputablePred fun c => c ∈ {c : Code | P c} := hP
  rcases (rice₂ {c : Code | P c} hsem).1 h with hemp | huniv
  · exact (Set.eq_empty_iff_forall_notMem.1 hemp c₁) hc₁
  · exact hc₂ (Set.eq_univ_iff_forall.1 huniv c₂)

/-- Semantic version: a nontrivial property `C` of partial functions, witnessed by two
partial recursive functions (one satisfying it, one not), is undecidable on programs. -/
theorem rice_nontrivial_partrec (C : Set (ℕ →. ℕ)) {f g : ℕ →. ℕ}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hfC : f ∈ C) (hgC : g ∉ C) :
    ¬ ComputablePred fun c => eval c ∈ C := fun h => hgC (rice C h hf hg hfC)


/-- An application: for each `n`, "the program halts on input `n`" is a nontrivial semantic
property, hence undecidable. -/
theorem halting_undecidable (n : ℕ) : ¬ ComputablePred fun c : Code => (eval c n).Dom := by
  refine rice_nontrivial _ (fun cf cg h => by rw [h]) ⟨⟨Code.zero, ?_⟩, ⟨?_, ?_⟩⟩
  · exact trivial
  · exact (exists_code.1 Nat.Partrec.none).choose
  · have h := (exists_code.1 Nat.Partrec.none).choose_spec
    simp [h]

end CS

