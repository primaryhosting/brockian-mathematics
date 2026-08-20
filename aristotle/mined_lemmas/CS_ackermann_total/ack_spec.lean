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

theorem ack_spec (m n : Nat) : Ack m n (ack m n) := by
  induction m, n using ack.induct with
  | case1 n => simpa using Ack.zero n
  | case2 m ih => exact Ack.succ_zero (by simpa using ih)
  | case3 m n ih₁ ih₂ => exact Ack.succ_succ ih₁ (by simpa using ih₂)

/-- Uniqueness: any value related to `(m, n)` by the graph relation equals
`ack m n`. -/
