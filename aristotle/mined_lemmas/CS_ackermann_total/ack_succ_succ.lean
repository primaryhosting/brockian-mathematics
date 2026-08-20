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

@[simp] theorem ack_succ_succ (m n : Nat) :
    ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]

/-- The graph of the Ackermann function, as an inductively defined relation:
`Ack m n v` holds exactly when the defining equations of the Ackermann function
derive the value `v` from the arguments `m` and `n`.  This relation is defined
without reference to any purported function, so proving that it relates each
pair `(m, n)` to exactly one value is precisely the statement that the
Ackermann recursion defines a total function. -/
inductive Ack : Nat → Nat → Nat → Prop
  | zero (n : Nat) : Ack 0 n (n + 1)
  | succ_zero {m r : Nat} : Ack m 1 r → Ack (m + 1) 0 r
  | succ_succ {m n r s : Nat} : Ack (m + 1) n r → Ack m r s → Ack (m + 1) (n + 1) s

/-- Existence: `ack m n` is a value related to `(m, n)` by the graph relation. -/
