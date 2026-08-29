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

set_option autoImplicit false

universe u v

namespace CS

open Language

/-- The complement automaton: same states, same transitions, same start state, but the set of
accepting states is complemented. -/

theorem eval_complDFA {α : Type u} {σ : Type v} (M : DFA α σ) (x : List α) :
    (complDFA M).eval x = M.eval x := rfl

/-- The complement automaton accepts exactly the complement of the language of `M`. -/
