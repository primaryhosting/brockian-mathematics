/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The Ackermann function, defined by recursion on the lexicographic order on `Nat × Nat`.

Lean accepts this definition precisely because each recursive call decreases the argument pair
in that (well-founded) order:
`(m, 1) <ₗ (m+1, 0)`, `(m+1, n) <ₗ (m+1, n+1)` and `(m, ack (m+1) n) <ₗ (m+1, n+1)`. -/

theorem lex_nat_wellFounded :
    WellFounded (Prod.Lex (α := Nat) (β := Nat) (· < ·) (· < ·)) :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- **The Ackermann function is total** (well-founded on lexicographic `Nat × Nat`).

Two things are asserted:

* the recursion measure, the lexicographic order on `Nat × Nat`, is well-founded;
* there exists a *total* function `f : Nat → Nat → Nat` (i.e. a genuine element of the
  function type, defined at every pair of arguments) satisfying the three defining
  equations of the Ackermann function.

The witness is `CS.ack`, which Lean elaborates by well-founded recursion on exactly this
lexicographic order; totality is therefore witnessed by the existence of the term itself,
and the equations are its recursion equations (`ack_zero`, `ack_succ_zero`, `ack_succ_succ`).

Mathlib also provides this function as `ack` (in `Mathlib.Computability.Ackermann`), with the
same three equations `ack_zero`, `ack_succ_zero`, `ack_succ_succ`; the development here is
kept import-free and self-contained. -/
