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

def DicksonConjecture : Prop :=
  ∀ (k : ℕ) (a b : ℕ → ℕ), (∀ i < k, 0 < b i) →
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ i < k, ¬ (p ∣ a i + b i * n)) →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∀ i < k, Nat.Prime (a i + b i * n)

/-- The `k`-tuple of linear forms `n + i · k!` (`i < k`), which computes the `k`-term
arithmetic progression with common difference `k!`, is admissible: for every prime `p`
there is an `n` making all `k` values coprime to `p`.

For `p ≤ k` one may take `n = 1`, since `p ∣ k!`.  For `p > k` the `k` forbidden residue
classes mod `p` cannot exhaust `ZMod p`, so a suitable residue exists. -/
