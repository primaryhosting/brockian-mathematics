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
