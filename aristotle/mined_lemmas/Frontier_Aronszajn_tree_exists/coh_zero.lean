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

theorem coh_zero (f g : Ordinal → ℕ) : Coh f g 0 :=
  Set.Finite.subset Set.finite_empty (fun x hx => absurd hx.1 (by simp))

/-! ### The limit stage -/

section LimitStage

variable {a : Ordinal} (ha : a < omega1) (h0 : a ≠ 0) (hs : ¬ ∃ b, a = b + 1)
  (IH : ∀ b < a, FinOne (E b) b ∧ ∀ c < b, Coh (E b) (E c) c)

include h0 hs in
