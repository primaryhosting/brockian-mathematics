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

theorem finOne_zero (f : Ordinal → ℕ) : FinOne f 0 := by
  intro v
  have : {x : Ordinal | x < 0 ∧ f x = v} = ∅ := by
    ext x; simp
  rw [this]; exact Set.finite_empty

