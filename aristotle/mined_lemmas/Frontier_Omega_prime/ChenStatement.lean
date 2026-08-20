/-
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `Omega n` is the number of prime factors of `n`, counted with multiplicity
(the classical arithmetic function `Ω`). -/

def ChenStatement : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → IsChenSum n

/-! ## Basic facts about `Omega` -/

