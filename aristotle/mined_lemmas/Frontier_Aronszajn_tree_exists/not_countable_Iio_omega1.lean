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

theorem not_countable_Iio_omega1 : ¬ (Set.Iio omega1).Countable :=
  fun h => lt_irrefl _ (lt_omega1_of_countable h)

