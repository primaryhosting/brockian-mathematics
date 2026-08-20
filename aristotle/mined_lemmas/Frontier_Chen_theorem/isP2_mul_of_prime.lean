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

theorem isP2_mul_of_prime {a b : ℕ} (ha : Nat.Prime a) (hb : Nat.Prime b) :
    IsP2 (a * b) := by
  simp [IsP2, Omega_mul_of_prime ha hb]

/-! ### A decidable search for Chen decompositions -/

/-- A Boolean search for a decomposition `n = p + q` with `p` prime and `q` either
prime or a product of two primes. -/
