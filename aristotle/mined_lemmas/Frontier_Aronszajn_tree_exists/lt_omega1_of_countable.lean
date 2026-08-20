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

theorem lt_omega1_of_countable {a : Ordinal} (h : (Set.Iio a).Countable) : a < omega1 := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal,
    Cardinal.lift_lt_aleph_one] at h
  exact Cardinal.lt_ord.mpr h

