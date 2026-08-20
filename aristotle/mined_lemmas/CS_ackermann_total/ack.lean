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

theorem Ack.eq_ack {m n v : Nat} (h : Ack m n v) : v = ack m n := by
  induction h with
  | zero n => simp
  | succ_zero _ ih => simpa using ih
  | succ_succ _ _ ih₁ ih₂ => subst ih₁; simpa using ih₂

/-- **The Ackermann function is total.**  For every pair of natural numbers
`(m, n)` the Ackermann recursion equations (encoded by the graph relation
`CS.Ack`) determine exactly one value: there exists a value `v` with
`Ack m n v`, and any `w` with `Ack m n w` equals `v`.  Well-foundedness of the
lexicographic order on `ℕ × ℕ` (`CS.lex_nat_wf`) is what makes the defining
recursion legitimate. -/
