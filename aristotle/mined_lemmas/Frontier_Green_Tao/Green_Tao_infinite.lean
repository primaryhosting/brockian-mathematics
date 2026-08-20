/-
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The Green–Tao theorem: *the primes contain arbitrarily long arithmetic progressions.*

This file contains

* the formal statement (`Frontier.HasArbitrarilyLongAPs Frontier.primeSet`, unfolded in
  `Frontier.GreenTaoStatement`);
* two Lean-checked reductions of it to standard conjectures, `Frontier.Green_Tao` (from the
  Erdős–Turán conjecture on arithmetic progressions, via Mathlib's divergence of the sum of
  prime reciprocals) and `Frontier.Green_Tao_of_Dickson` (from Dickson's conjecture on
  simultaneous primality of linear forms);
* unconditional base cases, `Frontier.Green_Tao_base`: an arithmetic progression of `k` primes
  exists for every `k ≤ 13`.

Every hypothesis is an explicit argument of the corresponding theorem; no axiom is introduced.
-/

namespace Frontier

/-- `IsAPIn A k a d` says that the `k`-term arithmetic progression with first term `a`
and common difference `d` is entirely contained in the set `A`. -/

theorem Green_Tao_infinite (hET : ErdosTuranAPConjecture) (k : ℕ) :
    {p : ℕ × ℕ | 0 < p.2 ∧ ∀ i < k, Nat.Prime (p.1 + i * p.2)}.Infinite :=
  GreenTaoStatement.infinite_APs (Green_Tao hET) k

/-! ### Unconditional base cases -/

/-- **Base cases of the Green–Tao theorem, unconditionally.**

For every `k ≤ 13` there is an arithmetic progression of `k` primes: the progression with
first term `4943` and common difference `60060`, namely
`4943, 65003, 125063, 185123, 245183, 305243, 365303, 425363, 485423, 545483, 605543, 665603,
725663`, consists of thirteen primes. -/
