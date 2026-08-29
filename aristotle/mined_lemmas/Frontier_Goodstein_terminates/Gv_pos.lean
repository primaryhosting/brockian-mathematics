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


theorem Gv_pos (b : ℕ) (w : Ordinal) (hw : 0 < w) (n : ℕ) (hn : n ≠ 0) : 0 < Gv b w n := by
  rw [Gv_def b w n hn]
  have h1 : (0 : Ordinal) < w ^ (Gv b w (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ)) := by
    apply mul_pos (opow_pos _ hw)
    exact_mod_cast nat_div_pow_log_pos b n hn
  exact lt_of_lt_of_le h1 le_self_add

/-- The main structural lemma: `Gv b w` is strictly monotone, and sends numbers below `b ^ k`
to ordinals below `w ^ (Gv b w k)`. -/
