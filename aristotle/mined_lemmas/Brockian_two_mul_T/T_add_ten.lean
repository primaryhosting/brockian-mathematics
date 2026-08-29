import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
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

namespace Brockian
namespace ConeLine

/-- The `n`-th triangular number. -/

lemma T_add_ten (n : ℕ) : T (n + 10) = T n + (10 * n + 55) := by
  have h : 2 * T (n + 10) = 2 * (T n + (10 * n + 55)) := by
    rw [two_mul_T (n + 10), mul_add 2 (T n) (10 * n + 55), two_mul_T n]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

