/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The lexicographic order on `ℕ × ℕ` is well-founded.  This is the order that
justifies the (non-structural) Ackermann recursion: each recursive call either
decreases the first component, or keeps it fixed and decreases the second. -/

theorem lex_nat_wf :
    WellFounded (Prod.Lex (· < ·) (· < ·) : Nat × Nat → Nat × Nat → Prop) :=
  ⟨fun (a, b) => Prod.lexAccessible (Nat.lt_wfRel.wf.apply a)
    (fun b => Nat.lt_wfRel.wf.apply b) b⟩

/-- The Ackermann function, defined by well-founded recursion on the
lexicographic order on `ℕ × ℕ`. -/
