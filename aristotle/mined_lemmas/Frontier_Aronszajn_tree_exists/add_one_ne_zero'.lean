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

theorem add_one_ne_zero' (b : Ordinal) : b + 1 ≠ 0 :=
  ne_of_gt (lt_of_le_of_lt (bot_le : (0 : Ordinal) ≤ b) (ord_lt_add_one b))

