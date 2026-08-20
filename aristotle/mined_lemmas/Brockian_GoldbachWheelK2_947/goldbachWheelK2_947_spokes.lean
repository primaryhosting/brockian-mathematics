/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because a module docstring may not
-- precede the `import` command in Lean 4; the text is otherwise verbatim.)

import Mathlib

namespace Brockian

/-- The list of "wheel spokes": the primes below `100`, used as the small summand
in the binary (`K = 2`) Goldbach decompositions below. -/

theorem goldbachWheelK2_947_spokes :
    ∀ n ∈ Finset.range 948, 4 ≤ n → n % 2 = 0 →
      ∃ p ∈ wheelSpokes, Nat.Prime p ∧ Nat.Prime (n - p) := by
  decide +kernel

/-- **Goldbach wheel, `K = 2`, bound `947`.**
Every even natural number `n` with `4 ≤ n ≤ 947` is the sum of two primes. -/
