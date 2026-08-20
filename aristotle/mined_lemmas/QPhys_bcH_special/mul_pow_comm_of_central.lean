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

lemma mul_pow_comm_of_central (hc : c = a * b - b * a) (hac : Commute a c) (m : ℕ) :
    b * a ^ m = a ^ m * b - (m : ℚ) • (c * a ^ (m - 1)) := by
  cases m with
  | zero => simp
  | succ n => simpa using mul_pow_succ_comm_of_central hc hac n

