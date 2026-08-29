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

theorem countable_Iio_iff (a : Ordinal.{0}) : (Set.Iio a).Countable ↔ a < ω₁ := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph_one,
    ← Cardinal.ord_aleph 1, Cardinal.lt_ord]

