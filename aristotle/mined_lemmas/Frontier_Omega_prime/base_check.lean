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

private theorem base_check :
    ∀ n ∈ Finset.Icc 4 500, Even n → ∃ p ∈ Finset.range (n + 1),
      Nat.Prime p ∧ Nat.Prime (n - p) := by
  decide

/-- **Base case, verified by computation.** Every even number `n` with `4 ≤ n ≤ 500` is a
Chen sum (indeed, a sum of two primes). -/
