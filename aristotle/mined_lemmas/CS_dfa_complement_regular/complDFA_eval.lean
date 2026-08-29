/-
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

universe u v

namespace CS

/-- The complement automaton of a DFA: same states, start state and transition function,
but with the set of accepting states complemented. -/

theorem complDFA_eval {α : Type u} {σ : Type v} (M : DFA α σ) (x : List α) :
    (complDFA M).eval x = M.eval x := rfl

/-- The complement automaton accepts exactly the complement language. -/
