import Mathlib
/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the very first command in a file, so the header
comment appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace QPhys

open Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The degree-`N` homogeneous component of the product `exp a * exp b`. -/

lemma bchCoef_zero_ne_zero (N : ℕ) : bchCoef N 0 ≠ 0 := by
  rw [bchCoef, if_pos (by omega)]
  simp [Nat.factorial_ne_zero]

/-- Downward induction on the power of `c`, used to show that `a + b` is nilpotent. -/
