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

theorem ord_lt_add_one (b : Ordinal) : b < b + 1 := by
  rw [Ordinal.add_one_eq_succ]; exact Order.lt_succ b

/-! ### Cofinal `ω`-sequences in countable limit ordinals -/

/-- A sequence hitting every ordinal below `a`, provided `Set.Iio a` is countable. -/
