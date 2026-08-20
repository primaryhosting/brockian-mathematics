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

theorem enumIio_lt {a : Ordinal} (ha : 0 < a) (n : ℕ) : enumIio a n < a := by
  unfold enumIio
  split
  · split
    · assumption
    · exact ha
  · exact ha

