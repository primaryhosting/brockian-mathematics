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

theorem ord_add_one_inj {b c : Ordinal} (h : b + 1 = c + 1) : b = c := by
  rw [Ordinal.add_one_eq_succ, Ordinal.add_one_eq_succ] at h
  exact Order.succ_injective h

