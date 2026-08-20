/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- The lexicographic order on `Nat × Nat` is well founded.  This is the termination
measure that justifies the recursive definition of the Ackermann function.  It follows
from the existing library lemma `Prod.lexAccessible` together with the well-foundedness
of `<` on `Nat` (`Nat.lt_wfRel`). -/

theorem lex_nat_nat_wellFounded :
    WellFounded (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)) :=
  ⟨fun p => Prod.lexAccessible (Nat.lt_wfRel.wf.apply p.1) Nat.lt_wfRel.wf.apply p.2⟩

/-- The Ackermann function, defined by well-founded recursion on the lexicographic
order of `Nat × Nat`. -/
