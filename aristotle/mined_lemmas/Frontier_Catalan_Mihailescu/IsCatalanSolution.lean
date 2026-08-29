import Mathlib
/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

/-- A *Catalan solution*: a pair of consecutive perfect powers, i.e. natural numbers with
`x ^ p = y ^ q + 1`, all of `x, y, p, q` being at least `2`. -/

def IsCatalanSolution (x p y q : ℕ) : Prop :=
  2 ≤ x ∧ 2 ≤ p ∧ 2 ≤ y ∧ 2 ≤ q ∧ x ^ p = y ^ q + 1

/-- `9 = 3 ^ 2` and `8 = 2 ^ 3` are consecutive perfect powers. -/
