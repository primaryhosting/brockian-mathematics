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

lemma mul_pow_succ_comm_of_central (hc : c = a * b - b * a) (hac : Commute a c) (m : ℕ) :
    b * a ^ (m + 1) = a ^ (m + 1) * b - ((m : ℚ) + 1) • (c * a ^ m) := by
  have hba : b * a = a * b - c := by rw [hc]; abel
  induction m with
  | zero => simp [hba]
  | succ n ih =>
    have h0 : b * a ^ (n + 2) = (b * a ^ (n + 1)) * a := by rw [pow_succ, ← mul_assoc]
    rw [h0, ih, sub_mul, mul_assoc, hba, smul_mul_assoc]
    have h1 : a ^ (n + 1) * (a * b - c) = a ^ (n + 2) * b - c * a ^ (n + 1) := by
      rw [mul_sub, ← mul_assoc, ← pow_succ, (hac.pow_left (n + 1)).eq]
    rw [h1, mul_assoc]
    push_cast
    rw [← pow_succ]
    module

/-- Moving `b` past a power of `a`, when the commutator `c = ab - ba` is central. -/
