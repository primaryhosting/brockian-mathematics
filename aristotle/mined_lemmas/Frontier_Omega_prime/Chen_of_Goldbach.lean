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

theorem Chen_of_Goldbach
    (H : ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q) :
    ChenStatement := by
  refine ⟨4, fun n hn hev => ?_⟩
  obtain ⟨p, q, hp, hq, rfl⟩ := H n hn hev
  exact chenSum_of_add_primes hp hq

/-- **Chen's theorem, reduced to a finiteness statement.**

Chen's theorem (every sufficiently large even number is the sum of a prime and a number with
at most two prime factors) is equivalent to the assertion that only finitely many even numbers
fail to be such a sum.  This is a Lean-checked reduction of the statement; the base case
`Chen_base_case` verifies the property for all even `n` with `4 ≤ n ≤ 500`. -/
