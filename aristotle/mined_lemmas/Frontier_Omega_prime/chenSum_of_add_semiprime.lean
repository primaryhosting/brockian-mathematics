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

theorem chenSum_of_add_semiprime {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) : IsChenSum (p + q * r) :=
  ⟨p, q * r, hp, by simp [Omega_mul_of_prime_of_prime hq hr], rfl⟩

/-! ## A Lean-checked base case -/

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
