import Mathlib
/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Ordinal

/-! ### Arithmetic preliminaries -/


theorem bump_ne_zero (b c n : ℕ) (hc : 0 < c) (hn : n ≠ 0) : bump b c n ≠ 0 := by
  have h : (0 : Ordinal) < Gv b (c : Ordinal) n := Gv_pos b _ (by exact_mod_cast hc) n hn
  rw [← natCast_bump] at h
  exact_mod_cast h.ne'

/-- Bumping the base does not change the ordinal value. -/
