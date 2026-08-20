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

theorem cseq_lt_succ (a : Ordinal) (n : ℕ) : cseq a n < cseq a (n + 1) := by
  rw [cseq_succ]
  exact lt_of_le_of_lt (le_max_left _ _) (ord_lt_add_one _)

