import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file contains auxiliary material used in the construction of an Aronszajn tree:
basic facts about countable ordinals, a dependent-choice helper, and the key
"extension" lemma for almost-disjoint modifications of injections into `ℕ`.
-/

namespace Aronszajn

open Set Cardinal Ordinal
open scoped Ordinal

/-! ### Countability of initial segments -/

/-- An initial segment of the ordinals is countable iff it lies below `ω₁`. -/

theorem not_countable_Iio_omega1 : ¬ (Set.Iio (ω₁ : Ordinal.{0})).Countable := by
  rw [countable_Iio_iff]
  exact lt_irrefl _

/-! ### A dependent choice helper -/

/-- Build a sequence by repeated choice, keeping an invariant and a step relation. -/
