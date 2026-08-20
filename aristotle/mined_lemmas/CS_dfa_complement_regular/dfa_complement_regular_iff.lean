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

theorem dfa_complement_regular_iff {T : Type} {L : Language T} :
    Lᶜ.IsRegular ↔ L.IsRegular :=
  ⟨fun h => L.compl_compl ▸ dfa_complement_regular h, dfa_complement_regular⟩

end CS

