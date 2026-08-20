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

theorem cseq_cofinal {a : Ordinal} (hc : (Set.Iio a).Countable) {x : Ordinal} (hx : x < a) :
    ∃ n, x < cseq a n := by
  obtain ⟨n, hn⟩ := enumIio_surj hc hx
  refine ⟨n + 1, ?_⟩
  rw [cseq_succ, ← hn]
  exact lt_of_le_of_lt (le_max_right _ _) (ord_lt_add_one _)

