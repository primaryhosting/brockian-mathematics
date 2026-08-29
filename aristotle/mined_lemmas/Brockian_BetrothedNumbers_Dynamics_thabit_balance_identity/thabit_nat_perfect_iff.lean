/-
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

For a Thabit-type candidate `m = (2 ^ k - 1) * (p + 2)` satisfying the delivered
sigma criterion `σ₁ m = (2 ^ (k + 1) - 1) * (p + 1)`, we prove the subtraction-free
balance identity

  `σ₁ m + 2 ^ (k + 1) = 2 * m + (p + 3)`

and deduce the deficient / perfect / abundant comparison `iff` theorems:
`m` is deficient (resp. perfect, abundant) exactly when `p + 3 < 2 ^ (k + 1)`
(resp. `=`, `>`).

The criterion is non-vacuous: `(k, p) = (4, 3)` gives `m = 75`, one half of the
betrothed (quasi-amicable) pair `(48, 75)`.
-/

set_option autoImplicit false

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- The Thabit-type candidate `m = (2 ^ k - 1) * (p + 2)`. -/

theorem thabit_nat_perfect_iff (k p : ℕ) (h : SigmaCriterion k p)
    (hpos : 0 < thabitCandidate k p) :
    Nat.Perfect (thabitCandidate k p) ↔ p + 3 = 2 ^ (k + 1) := by
  rw [Nat.perfect_iff_sigma_eq_two_mul hpos, ← sigma_one_eq_sigmaOne]
  exact thabit_perfect_iff k p h

/-- The sigma criterion is non-vacuous: it holds for `(k, p) = (4, 3)`, i.e. for
`m = 15 * 5 = 75`. -/
