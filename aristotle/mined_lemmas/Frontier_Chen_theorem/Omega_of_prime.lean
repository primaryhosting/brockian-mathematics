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

theorem Omega_of_prime {p : ℕ} (hp : Nat.Prime p) : Omega p = 1 := by
  simp [Omega, Nat.primeFactorsList_prime hp]

