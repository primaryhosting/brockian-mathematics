/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Ordinal

/-! ## Elementary facts about base-`b` digits -/


theorem digit_lt {b n : ℕ} (hb : 2 ≤ b) : n / b ^ Nat.log b n < b := by
  have h := Nat.lt_pow_succ_log_self (b := b) hb n
  rw [Nat.div_lt_iff_lt_mul (pow_log_pos b n)]
  simpa [pow_succ, Nat.mul_comm] using h

/-! ## A generic hereditary base-`b` evaluation -/

/-- `hval b pw mul n` is the value of the hereditary base-`b` representation of `n`,
where the "power" operation is interpreted by `pw` and multiplication by a digit by `mul`. -/
