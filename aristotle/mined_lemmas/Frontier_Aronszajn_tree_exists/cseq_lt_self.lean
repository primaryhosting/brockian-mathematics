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

theorem cseq_lt_self (n : ℕ) : cseq a n < a :=
  cseq_lt_of_limit (limit_props h0 hs).1 (limit_props h0 hs).2 n

