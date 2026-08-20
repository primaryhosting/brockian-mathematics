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

namespace Math

open Complex Polynomial Finset

/-- The sum of the primitive `3`-rd roots of unity in `ℂ` equals `μ(3) = -1`. -/

theorem mobius_root_sum_3 :
    ∑ z ∈ primitiveRoots 3 ℂ, z = (ArithmeticFunction.moebius 3 : ℂ) := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hζdef
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) 3 := hζ.pow_of_coprime 2 (by decide)
  have hne : ζ ≠ ζ ^ 2 := by
    intro h
    have := hζ.pow_inj (i := 1) (j := 2) (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hsub : ({ζ, ζ ^ 2} : Finset ℂ) ⊆ primitiveRoots 3 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 hζ
    · exact (mem_primitiveRoots (by norm_num)).2 hζ2
  have hcard : #(primitiveRoots 3 ℂ) = 2 := by
    rw [hζ.card_primitiveRoots]; decide
  have heq : primitiveRoots 3 ℂ = ({ζ, ζ ^ 2} : Finset ℂ) := by
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hcard, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := by
    intro h
    have := hζ.pow_inj (i := 0) (j := 1) (by norm_num) (by norm_num) (by simpa using h.symm)
    omega
  have hsum : ζ + ζ ^ 2 = -1 := by
    have hfac : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by ring_nf; linear_combination h3
    have : ζ ^ 2 + ζ + 1 = 0 := by
      rcases mul_eq_zero.1 hfac with h | h
      · exact absurd (sub_eq_zero.1 h) hζ1
      · exact h
    linear_combination this
  rw [heq, Finset.sum_insert (by simpa using hne), Finset.sum_singleton, hsum]
  norm_num [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)]

end Math

