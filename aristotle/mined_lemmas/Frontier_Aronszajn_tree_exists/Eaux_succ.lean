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

theorem Eaux_succ (a : Ordinal) (n : ℕ) (x : Ordinal) :
    Eaux a (n + 1) x = if x < cseq a n then Eaux a n x else max (E (cseq a (n + 1)) x) n := rfl

