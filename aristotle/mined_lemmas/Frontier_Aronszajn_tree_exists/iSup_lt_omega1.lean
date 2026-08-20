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

theorem iSup_lt_omega1 {f : ℕ → Ordinal} (h : ∀ n, f n < omega1) : iSup f < omega1 :=
  Ordinal.iSup_sequence_lt_omega_one f h

