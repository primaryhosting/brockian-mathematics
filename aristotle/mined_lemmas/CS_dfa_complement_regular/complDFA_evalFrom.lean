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

theorem complDFA_evalFrom {T σ : Type} (M : DFA T σ) (s : σ) (x : List T) :
    (complDFA M).evalFrom s x = M.evalFrom s x := rfl

/-- The complement DFA accepts exactly the complement of the language of `M`. -/
