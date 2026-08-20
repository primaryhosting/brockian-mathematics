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

private theorem chenCheck_range :
    ∀ n ∈ List.range (chenBound + 1), (n % 2 = 0 ∧ 4 ≤ n) → chenCheck n = true := by
  decide

/-- **Base case of Chen's theorem.**  Every even number `n` with `4 ≤ n ≤ 500` is of the
form `p + q` with `p` prime and `q` a prime or a product of two primes. -/
