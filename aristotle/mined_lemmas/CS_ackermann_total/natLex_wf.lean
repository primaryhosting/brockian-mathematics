/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- The lexicographic order on `Nat × Nat`, the measure used for the Ackermann recursion. -/
abbrev natLex : Nat × Nat → Nat × Nat → Prop := Prod.Lex Nat.lt Nat.lt

/-- The lexicographic order on `Nat × Nat` is well-founded. -/

theorem natLex_wf : WellFounded natLex :=
  WellFounded.intro fun p =>
    Prod.lexAccessible (Nat.lt_wfRel.wf.apply p.1) (fun b => Nat.lt_wfRel.wf.apply b) p.2

/-- The Ackermann function, defined by well-founded recursion on `natLex`. -/
