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

theorem limit_props {a : Ordinal} (h0 : a ≠ 0) (hs : ¬ ∃ b, a = b + 1) :
    0 < a ∧ ∀ b < a, b + 1 < a := by
  refine ⟨lt_of_le_of_ne (bot_le : (0 : Ordinal) ≤ a) (Ne.symm h0), fun b hb => ?_⟩
  have h1 : b + 1 ≤ a := by simpa [Ordinal.add_one_eq_succ] using Order.succ_le_of_lt hb
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exact absurd ⟨b, h.symm⟩ hs

/-! ### The coherent family `E` -/

/-- One step of the transfinite recursion producing the coherent family `E`. -/
