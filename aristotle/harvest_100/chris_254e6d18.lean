/-
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Finset

namespace Math

/-- The sum of the primitive `9`-th roots of unity in `ℂ` equals `μ(9) = 0`.

The proof writes the primitive 9-th roots as `ζ ^ i` for `i ∈ {1,2,4,5,7,8}` where
`ζ = exp(2πi/9)` (via `IsPrimitiveRoot.isPrimitiveRoot_iff`), and then uses
`IsPrimitiveRoot.geom_sum_eq_zero` for `ζ` (order 9) and for `ζ ^ 3` (order 3). -/
theorem mobius_root_sum_9 :
    ∑ z ∈ primitiveRoots 9 ℂ, z = (ArithmeticFunction.moebius 9 : ℂ) := by
  classical
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9) with hζdef
  have hζ : IsPrimitiveRoot ζ 9 := Complex.isPrimitiveRoot_exp 9 (by norm_num)
  have hset : primitiveRoots 9 ℂ = ({1, 2, 4, 5, 7, 8} : Finset ℕ).image (fun i => ζ ^ i) := by
    ext x
    rw [mem_primitiveRoots (by norm_num), hζ.isPrimitiveRoot_iff]
    constructor
    · rintro ⟨i, hi, hic, rfl⟩
      refine mem_image.2 ⟨i, ?_, rfl⟩
      interval_cases i <;> simp_all [Nat.Coprime]
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      fin_cases hi <;> exact ⟨_, by norm_num, by decide, rfl⟩
  rw [hset, Finset.sum_image (by
    intro i hi j hj hij
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hi hj
    have hi' : i < 9 := by omega
    have hj' : j < 9 := by omega
    exact hζ.pow_inj hi' hj' hij)]
  have h9 : ∑ i ∈ Finset.range 9, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have h3 : IsPrimitiveRoot (ζ ^ 3) 3 := by
    have := hζ.pow_of_dvd (p := 3) (by norm_num) (by norm_num)
    norm_num at this
    exact this
  have h3' : ∑ i ∈ Finset.range 3, (ζ ^ 3) ^ i = 0 := h3.geom_sum_eq_zero (by norm_num)
  simp [Finset.sum_range_succ, ← pow_mul] at h9 h3' ⊢
  have hm : (ArithmeticFunction.moebius 9) = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    have := h 3 ⟨1, by norm_num⟩
    rw [Nat.isUnit_iff] at this
    omega
  rw [hm]
  push_cast
  linear_combination h9 - h3'

end Math

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

