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

theorem Omega_mul_of_prime_of_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    Omega (p * q) = 2 := by
  have h := Nat.perm_primeFactorsList_mul hp.ne_zero hq.ne_zero
  simp [Omega, h.length_eq, Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hq]

/-- A prime is in particular a number with at most two prime factors. -/
