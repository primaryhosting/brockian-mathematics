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


theorem natCast_bump (b c n : ℕ) : ((bump b c n : ℕ) : Ordinal) = Gv b (c : Ordinal) n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [bump_def b c n hn, Gv_def b (c : Ordinal) n hn, ← IH _ (Nat.log_lt_self b hn),
        ← IH _ (nat_mod_pow_log_lt b n hn), Nat.cast_add, Ordinal.natCast_mul,
        natCast_pow_ord]

