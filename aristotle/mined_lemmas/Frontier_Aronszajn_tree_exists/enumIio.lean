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

noncomputable def enumIio (a : Ordinal) (n : ℕ) : Ordinal :=
  if h : ∃ g : ℕ → Ordinal, ∀ x < a, ∃ m, g m = x then
    (if h.choose n < a then h.choose n else 0)
  else 0

