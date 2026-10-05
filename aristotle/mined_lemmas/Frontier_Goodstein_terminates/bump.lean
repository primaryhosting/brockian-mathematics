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


def bump (b c : ℕ) : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>
      c ^ (bump b c (Nat.log b (n + 1))) * ((n + 1) / b ^ Nat.log b (n + 1))
        + bump b c ((n + 1) % b ^ Nat.log b (n + 1))
  decreasing_by
    · exact Nat.log_lt_self b (Nat.succ_ne_zero n)
    · exact nat_mod_pow_log_lt b (n + 1) (Nat.succ_ne_zero n)

