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

theorem ack_eq_mathlib_ack : ∀ m n, CS.ack m n = _root_.ack m n
  | 0, n => by simp
  | m + 1, 0 => by
      simp [ack_eq_mathlib_ack m 1]
  | m + 1, n + 1 => by
      rw [CS.ack_succ_succ, _root_.ack_succ_succ, ack_eq_mathlib_ack (m + 1) n,
        ack_eq_mathlib_ack m _]

end CS

