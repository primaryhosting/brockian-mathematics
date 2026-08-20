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

private lemma neg_of_abs_add_le_one {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (h : |a + b| ≤ 1) : b = -a := by
  rw [abs_le] at h
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb <;> omega

/-- **Base case of the Erdős discrepancy problem (`C = 1`).**
For every `±1`-sequence `f` there are a common difference `d ≥ 1` and a length `n ≥ 1`
such that the discrepancy `|f d + f (2d) + ⋯ + f (nd)|` is at least `2`.

Moreover the progression can be taken inside `{1, …, 12}` (i.e. `d * n ≤ 12`), which is
optimal: see `Frontier.exists_discrepancy_le_one_up_to_eleven`. This is the `C = 1`
instance of `Frontier.ErdosDiscrepancyStatement`. -/
