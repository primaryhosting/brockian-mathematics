import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header block above
-- appears immediately after the single `import Mathlib` line.)

set_option maxRecDepth 10000

namespace Frontier

/-- `IsPrimeAP k a d` says that `a, a + d, …, a + (k-1) d` is an arithmetic progression of
length `k` consisting of prime numbers, with positive common difference `d`. -/

def IsPrimeAP (k a d : ℕ) : Prop := 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d)

/-- The Green–Tao theorem: the primes contain arbitrarily long arithmetic progressions. -/
