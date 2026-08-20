import Mathlib

/-!
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex

namespace Math

/-- The set of primitive `3`-rd roots of unity in `ℂ` consists of `ζ` and `ζ ^ 2`, for any
primitive `3`-rd root of unity `ζ`. -/
lemma primitiveRoots_three_eq {ζ : ℂ} (h : IsPrimitiveRoot ζ 3) :
    primitiveRoots 3 ℂ = {ζ, ζ ^ 2} := by
  ext z
  rw [mem_primitiveRoots (by norm_num), h.isPrimitiveRoot_iff, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, hcop, rfl⟩
    interval_cases i
    · exact absurd hcop (by decide)
    · exact Or.inl (pow_one ζ)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨1, by norm_num, by norm_num, pow_one _⟩
    · exact ⟨2, by norm_num, by norm_num, rfl⟩

/-- The sum of the primitive `3`-rd roots of unity in `ℂ` equals `μ 3 = -1`. -/
theorem mobius_root_sum_3 :
    ∑ z ∈ primitiveRoots 3 ℂ, z = (ArithmeticFunction.moebius 3 : ℤ) := by
  have h : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hne : ζ ≠ ζ ^ 2 := by
    intro hcon
    have := h.pow_inj (i := 1) (j := 2) (by norm_num) (by norm_num) (by rwa [pow_one])
    omega
  have hgeom : ∑ i ∈ Finset.range 3, ζ ^ i = 0 := h.geom_sum_eq_zero (by norm_num)
  rw [primitiveRoots_three_eq h, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hgeom
  push_cast
  linear_combination hgeom

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

