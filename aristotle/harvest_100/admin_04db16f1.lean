/-
# Det Eq Mertens 3
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Riemann.Redheffer

/-- The `3 × 3` Redheffer matrix (0-indexed): `R i j = 1` when `j = 0` or
`(i+1) ∣ (j+1)`, and `0` otherwise. -/
def R : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- `det R = -1 = M(3)`, the Mertens function at `3`. -/
theorem det_eq_mertens_3 : R.det = -1 := by
  rw [Matrix.det_fin_three]
  simp [R]

/-- The Mertens function value `M 3 = μ 1 + μ 2 + μ 3 = -1`, matching `det R`. -/
theorem det_eq_mertens_sum_3 :
    R.det = ∑ n ∈ Finset.Icc 1 3, ArithmeticFunction.moebius n := by
  have h : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  rw [det_eq_mertens_3, h]
  simp [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)]

end Riemann.Redheffer

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

