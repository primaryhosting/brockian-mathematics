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

noncomputable def cseq (a : Ordinal) : ℕ → Ordinal
  | 0 => 0
  | (n + 1) => max (cseq a n) (enumIio a n) + 1

