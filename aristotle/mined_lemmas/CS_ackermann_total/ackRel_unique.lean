/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The Ackermann function, defined by recursion on the lexicographic order on `ℕ × ℕ`
(the `termination_by (m, n)` clause below; well-foundedness of that order is recorded
separately as `CS.wellFounded_lex_nat`). -/

theorem ackRel_unique {m n k : Nat} (h : AckRel m n k) : k = ack m n := by
  induction h with
  | zero n => simp
  | succ_zero _ ih => simpa using ih
  | succ_succ _ _ ih₁ ih₂ => subst ih₁; simpa using ih₂

/-- **The Ackermann function is total.**  The Ackermann recursion, which is well founded
for the lexicographic order on `ℕ × ℕ` (`CS.wellFounded_lex_nat`), determines exactly one
value at every pair of natural numbers: for all `m n` there is a unique `k` with
`AckRel m n k`, namely `k = ack m n`. -/
