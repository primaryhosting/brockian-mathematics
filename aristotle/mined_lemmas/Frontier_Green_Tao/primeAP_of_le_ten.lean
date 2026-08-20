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

theorem primeAP_of_le_ten {k : ℕ} (hk : k ≤ 10) : PrimeAP k :=
  primeAP_ten.mono hk

/-- **Green–Tao, formalized statement together with a Lean-checked reduction.**

The primes contain arbitrarily long arithmetic progressions *if and only if* they contain
arbitrarily long arithmetic progressions arbitrarily far out (all of whose terms exceed any
prescribed bound `N`).  Thus the seemingly stronger "infinitely often" form of the Green–Tao
