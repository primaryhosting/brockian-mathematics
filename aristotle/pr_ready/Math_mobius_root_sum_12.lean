/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Statement: The sum of the primitive 12-th roots of unity equals μ(12).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open Finset

namespace Math

/-- The sum of the primitive 12-th roots of unity in `ℂ` equals `μ(12)` (which is `0`,
since `12 = 2^2 * 3` is not squarefree).

The proof pairs each primitive 12-th root of unity `x` with `-x = x ^ 7`, which is again a
primitive 12-th root of unity; hence the sum equals its own negative. -/
theorem mobius_root_sum_12 :
    ∑ z ∈ primitiveRoots 12 ℂ, z = ((ArithmeticFunction.moebius 12 : ℤ) : ℂ) := by
  have hneg : ∀ x ∈ primitiveRoots 12 ℂ, -x ∈ primitiveRoots 12 ℂ := by
    intro x hx
    rw [mem_primitiveRoots (by norm_num)] at hx ⊢
    have h12 : (x ^ 6 - 1) * (x ^ 6 + 1) = 0 := by
      have : (x ^ 6) ^ 2 = 1 := by rw [← pow_mul]; exact hx.pow_eq_one
      linear_combination this
    have hne : x ^ 6 - 1 ≠ 0 := by
      intro h
      have := (hx.pow_eq_one_iff_dvd 6).1 (by linear_combination h)
      omega
    have h6 : x ^ 6 = -1 := by
      have := (mul_eq_zero.1 h12).resolve_left hne
      linear_combination this
    have hx7 : -x = x ^ 7 := by
      rw [show (7:ℕ) = 6 + 1 from rfl, pow_succ, h6]; ring
    rw [hx7]
    exact hx.pow_of_coprime 7 (by norm_num)
  have key : ∑ z ∈ primitiveRoots 12 ℂ, z = ∑ z ∈ primitiveRoots 12 ℂ, (-z) :=
    Finset.sum_nbij' (fun x => -x) (fun x => -x) hneg hneg (by simp) (by simp) (by simp)
  rw [Finset.sum_neg_distrib] at key
  have h2 : (2 : ℂ) * ∑ z ∈ primitiveRoots 12 ℂ, z = 0 := by linear_combination key
  have hs : ∑ z ∈ primitiveRoots 12 ℂ, z = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · norm_num at h
    · exact h
  rw [hs, ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)]
  norm_num

end Math

