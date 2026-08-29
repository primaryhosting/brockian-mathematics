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

theorem ack_recursion_decreasing (m n v : Nat) :
    natLex (m, 1) (m + 1, 0) ∧ natLex (m + 1, n) (m + 1, n + 1) ∧
      natLex (m, v) (m + 1, n + 1) :=
  ⟨Prod.Lex.left _ _ (Nat.lt_succ_self m), Prod.Lex.right _ (Nat.lt_succ_self n),
    Prod.Lex.left _ _ (Nat.lt_succ_self m)⟩

/-- The graph of the Ackermann recursion: `AckGraph m n v` holds when the defining
equations force the value of the Ackermann function at `(m, n)` to be `v`. -/
inductive AckGraph : Nat → Nat → Nat → Prop
  | zero (n : Nat) : AckGraph 0 n (n + 1)
  | succ_zero {m v : Nat} : AckGraph m 1 v → AckGraph (m + 1) 0 v
  | succ_succ {m n v w : Nat} :
      AckGraph (m + 1) n v → AckGraph m v w → AckGraph (m + 1) (n + 1) w

/-- Existence: `ack m n` satisfies the Ackermann recursion at every point. -/
