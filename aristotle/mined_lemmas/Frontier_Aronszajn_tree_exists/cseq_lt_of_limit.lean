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

theorem cseq_lt_of_limit {a : Ordinal} (h0 : 0 < a) (hl : ∀ b < a, b + 1 < a) (n : ℕ) :
    cseq a n < a := by
  induction n with
  | zero => simpa [cseq_zero] using h0
  | succ n ih => rw [cseq_succ]; exact hl _ (max_lt ih (enumIio_lt h0 n))

