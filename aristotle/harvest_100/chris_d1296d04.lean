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

import Mathlib

/-!
# Sum of the primitive 12-th roots of unity

The sum of the primitive 12-th roots of unity in `ℂ` equals `μ 12`, the Möbius
function evaluated at `12` (which is `0`, since `12 = 2^2 * 3` is not squarefree).

The proof pairs each primitive 12-th root `z` with `-z = z ^ 7`, which is again a
primitive 12-th root and distinct from `z`; the sum therefore vanishes.
-/

namespace Math

/-- The sum of the primitive 12-th roots of unity equals `μ 12`. -/
theorem mobius_root_sum_12 :
    ∑ z ∈ primitiveRoots 12 ℂ, z = (ArithmeticFunction.moebius 12 : ℂ) := by
  have hmu : (ArithmeticFunction.moebius 12 : ℤ) = 0 := by decide
  rw [hmu]
  push_cast
  refine Finset.sum_involution (fun z _ => -z) ?_ ?_ ?_ ?_
  · intro z hz; simp
  · intro z hz hz0 h
    simp only at h
    exact hz0 (by linear_combination (-1 / 2 : ℂ) * h)
  · intro z hz
    simp only
    rw [mem_primitiveRoots (by norm_num)] at hz ⊢
    have h6 : z ^ 6 = -1 := by
      have h12 : (z ^ 6 - 1) * (z ^ 6 + 1) = 0 := by
        have := hz.pow_eq_one
        linear_combination this
      rcases mul_eq_zero.1 h12 with h | h
      · exfalso
        have hc : z ^ 6 = 1 := by linear_combination h
        have := (hz.pow_eq_one_iff_dvd 6).1 hc
        omega
      · linear_combination h
    have hz7 : -z = z ^ 7 := by
      rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, h6]; ring
    rw [hz7]
    exact hz.pow_of_coprime 7 (by decide)
  · intro z hz; simp

end Math

