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

theorem E_succ (b x : Ordinal) : E (b + 1) x = if x < b then E b x else 0 := by
  have hs : ∃ c, b + 1 = c + 1 := ⟨b, rfl⟩
  have hc : hs.choose = b := (ord_add_one_inj hs.choose_spec).symm
  rw [E_eq]; unfold Estep
  rw [dif_neg (add_one_ne_zero' b), dif_pos hs]
  simp only [hc]

/-- The `ω`-approximation sequence used at limit stages of the recursion. -/
