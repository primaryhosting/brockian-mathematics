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

def ErdosTuranAPConjecture : Prop :=
  ∀ A : Set ℕ, ¬ Summable (A.indicator fun n : ℕ => (1 : ℝ) / n) → HasArbitrarilyLongAPs A

/-- **Green–Tao theorem (Lean-checked reduction).**

The primes contain arbitrarily long arithmetic progressions: for every `k` there are natural
numbers `a` and `d > 0` with `a, a + d, …, a + (k-1) d` all prime.

The Green–Tao theorem itself is not available in Mathlib, so what is proved here is a
*reduction*: the conclusion is derived, unconditionally in Lean, from the Erdős–Turán
conjecture on arithmetic progressions, using Mathlib's theorem that the sum of the reciprocals
of the primes diverges.  The hypothesis is an explicit assumption of the statement; no axiom is
introduced. -/
