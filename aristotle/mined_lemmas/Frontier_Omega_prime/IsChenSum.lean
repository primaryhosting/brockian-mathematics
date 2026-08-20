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

def IsChenSum (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Omega q ≤ 2 ∧ n = p + q

/-- Chen's theorem: every sufficiently large even number is the sum of a prime and a
number with at most two prime factors. -/
