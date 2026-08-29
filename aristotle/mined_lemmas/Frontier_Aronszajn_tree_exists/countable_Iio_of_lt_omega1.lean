/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/

theorem countable_Iio_of_lt_omega1 {α : Ordinal} (h : α < ω₁) : (Set.Iio α).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one]
  have := Cardinal.lt_omega_iff_card_lt.mp h
  simpa [Ordinal.card, Ordinal.mk_Iio_ordinal] using this

