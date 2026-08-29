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


theorem nat_div_pow_log_lt (b n : ℕ) (hb : 2 ≤ b) : n / b ^ Nat.log b n < b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using lt_of_lt_of_le Nat.zero_lt_two hb
  · have h := Nat.lt_pow_succ_log_self (b := b) hb n
    rw [Nat.div_lt_iff_lt_mul (nat_pow_log_pos b n)]
    simpa [pow_succ, Nat.mul_comm] using h

/-- Uniqueness of the base-`c` decomposition, in the form we need. -/
