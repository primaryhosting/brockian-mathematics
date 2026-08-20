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

lemma bchL_eq_zero {K N : ℕ} (hKa : a ^ K = 0) (hKb : b ^ K = 0) (hN : 2 * K ≤ N) :
    bchL a b N = 0 := by
  refine Finset.sum_eq_zero fun m hm => ?_
  rcases le_or_gt K m with h | h
  · rw [pow_eq_zero_of_le h hKa, zero_mul, smul_zero]
  · rw [pow_eq_zero_of_le (by omega : K ≤ N - m) hKb, mul_zero, smul_zero]

/-- The commutator of two nilpotent elements with central commutator is nilpotent. -/
