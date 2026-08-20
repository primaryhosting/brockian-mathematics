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

theorem Eaux_stable {m n : ℕ} (hmn : m ≤ n) {x : Ordinal} (hx : x < cseq a m) :
    Eaux a n x = Eaux a m x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [Eaux_succ, if_pos (lt_of_lt_of_le hx ((cseq_mono a).monotone hmn)), ih]

include h0 hs in
