/-
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Language

/-- The complement DFA: same transitions and start state, complemented accepting set. -/
def complDFA {T σ : Type} (M : DFA T σ) : DFA T σ where
  step := M.step
  start := M.start
  accept := M.acceptᶜ

@[simp]
theorem complDFA_evalFrom {T σ : Type} (M : DFA T σ) (s : σ) (x : List T) :
    (complDFA M).evalFrom s x = M.evalFrom s x := rfl

/-- The complement DFA accepts exactly the complement of the language of `M`. -/
theorem accepts_complDFA {T σ : Type} (M : DFA T σ) :
    (complDFA M).accepts = (M.accepts)ᶜ :=
  Set.ext fun _ => Iff.rfl

/-- **Regular languages are closed under complement.**

If `L` is regular (accepted by some DFA with finitely many states), then so is `Lᶜ`.
The proof is the standard construction: keep the same automaton and complement its
set of accepting states.

Mathlib also provides this as `Language.IsRegular.compl` (and the `simp` lemma
`Language.IsRegular_compl`); here we give the construction explicitly. -/
theorem dfa_complement_regular {T : Type} {L : Language T} (h : L.IsRegular) :
    Lᶜ.IsRegular := by
  obtain ⟨σ, hσ, M, hM⟩ := h
  exact ⟨σ, hσ, complDFA M, by rw [accepts_complDFA, hM]⟩

/-- The complement version, as an iff: `Lᶜ` is regular iff `L` is. -/
theorem dfa_complement_regular_iff {T : Type} {L : Language T} :
    Lᶜ.IsRegular ↔ L.IsRegular :=
  ⟨fun h => L.compl_compl ▸ dfa_complement_regular h, dfa_complement_regular⟩

end CS

