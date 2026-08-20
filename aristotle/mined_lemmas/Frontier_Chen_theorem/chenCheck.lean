import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `Omega n` is the number of prime factors of `n`, counted with multiplicity
(the classical arithmetic function `Ω`). -/

def chenCheck (n : ℕ) : Bool :=
  (List.range (n + 1)).any fun p => decide (Nat.Prime p) && decide (p ≤ n) &&
    ((decide (Nat.Prime (n - p))) || (List.range (n + 1)).any fun a =>
        decide (Nat.Prime a) && ((n - p) % a == 0) && decide (Nat.Prime ((n - p) / a)))

