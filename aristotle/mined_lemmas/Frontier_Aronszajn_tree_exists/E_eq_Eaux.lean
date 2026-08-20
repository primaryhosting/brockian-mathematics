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

theorem E_eq_Eaux {n : ℕ} {x : Ordinal} (hx : x < cseq a n) : E a x = Eaux a n x := by
  have hex : ∃ k, x < cseq a k := ⟨n, hx⟩
  rw [E_limit h0 hs x, dif_pos hex]
  exact (Eaux_stable (Nat.find_le hx) (Nat.find_spec hex)).symm

include h0 hs IH in
