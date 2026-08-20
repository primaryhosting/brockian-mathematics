/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A `±1`-sequence: a function `f : ℕ → ℤ` all of whose values on positive integers
are `1` or `-1`. -/

private lemma extremalEleven_bound_aux :
    ∀ d ∈ Finset.Icc 1 11, ∀ n ∈ Finset.Icc 1 11, d * n ≤ 11 →
      |apSum extremalEleven d n| ≤ 1 := by
  decide

/-- **Optimality of the base case.** There is a `±1`-sequence all of whose homogeneous
arithmetic progressions inside `{1, …, 11}` have sum of absolute value at most `1`.
Hence `Frontier.erdos_discrepancy` cannot be witnessed using fewer than `12` terms. -/
