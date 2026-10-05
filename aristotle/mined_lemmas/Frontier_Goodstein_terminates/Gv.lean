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


noncomputable def Gv (b : ℕ) (w : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | (n + 1) =>
      w ^ (Gv b w (Nat.log b (n + 1))) * ((n + 1) / b ^ Nat.log b (n + 1) : ℕ)
        + Gv b w ((n + 1) % b ^ Nat.log b (n + 1))
  decreasing_by
    · exact Nat.log_lt_self b (Nat.succ_ne_zero n)
    · exact nat_mod_pow_log_lt b (n + 1) (Nat.succ_ne_zero n)

