/-
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e` of `ZMod 5` with values in `ℂ`, `e x = ω ^ x.val`. -/

theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  have hcard : ((raySum S r : ℕ) : ℂ) = ∑ n ∈ S, if (n : ZMod 5) = r then (1 : ℂ) else 0 := by
    rw [raySum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => rayIndicator_eq_charSum n r

end Brockian.Characters5

