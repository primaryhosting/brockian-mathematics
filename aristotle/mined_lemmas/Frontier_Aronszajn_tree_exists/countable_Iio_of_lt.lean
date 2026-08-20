/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Ordinal Set Cardinal
open scoped Classical

namespace Frontier

/-- The first uncountable ordinal `ω₁`. -/

theorem countable_Iio_of_lt {a : Ordinal} (h : a < omega1) : (Set.Iio a).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph_one]
  exact Cardinal.lt_ord.mp h

