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

theorem chenSum_of_add_primes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    IsChenSum (p + q) :=
  ⟨p, q, hp, by simp [Omega_prime hq], rfl⟩

/-- A product of two primes has at most two prime factors, so `p + q * r` is a Chen sum. -/
