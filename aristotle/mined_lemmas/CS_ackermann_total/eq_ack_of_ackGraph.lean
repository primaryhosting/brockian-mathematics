/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The lexicographic order on `Nat × Nat`, used as the termination measure for the Ackermann
recursion. -/

theorem eq_ack_of_ackGraph {m n v : Nat} (h : AckGraph m n v) : v = ack m n := by
  induction h with
  | zero n => simp
  | succZero _ ih => simpa using ih
  | succSucc _ _ ih₁ ih₂ => subst ih₁; simpa using ih₂

/-- **The Ackermann function is total.**

The Ackermann recursion, whose recursive calls all decrease in the (well-founded, see
`CS.lexNat_wf`) lexicographic order on `Nat × Nat`, determines exactly one output value for every
pair of inputs: for all `m n : Nat` there is a unique `v` with `AckGraph m n v`. -/
