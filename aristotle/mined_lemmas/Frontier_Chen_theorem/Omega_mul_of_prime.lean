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

theorem Omega_mul_of_prime {a b : ℕ} (ha : Nat.Prime a) (hb : Nat.Prime b) :
    Omega (a * b) = 2 := by
  have h := Nat.perm_primeFactorsList_mul ha.ne_zero hb.ne_zero
  simp [Omega, h.length_eq, Nat.primeFactorsList_prime ha, Nat.primeFactorsList_prime hb]

