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

def IsChenNumber (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ IsP2 q ∧ n = p + q

/-- The full statement of Chen's theorem: every sufficiently large even number `n`
is of the form `p + q` with `p` prime and `q` having at most two prime factors. -/
