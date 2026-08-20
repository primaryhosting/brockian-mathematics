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

theorem accepts_complDFA {T σ : Type} (M : DFA T σ) :
    (complDFA M).accepts = (M.accepts)ᶜ :=
  Set.ext fun _ => Iff.rfl

/-- **Regular languages are closed under complement.**

If `L` is regular (accepted by some DFA with finitely many states), then so is `Lᶜ`.
The proof is the standard construction: keep the same automaton and complement its
set of accepting states.

Mathlib also provides this as `Language.IsRegular.compl` (and the `simp` lemma
`Language.IsRegular_compl`); here we give the construction explicitly. -/
