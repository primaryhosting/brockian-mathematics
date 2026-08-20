import Mathlib
/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- `PrimeAP k` says that the primes contain an arithmetic progression of length `k`:
there are `a` and a positive common difference `d` with `a + i * d` prime for all `i < k`. -/

theorem is equivalent to the plain form, and proving the plain form for every length `k`
suffices.  The plain form itself is verified here only for lengths `k ≤ 10`
(see `Frontier.primeAP_of_le_ten`); the general case is the Green–Tao theorem, which is not
available in Mathlib. -/
