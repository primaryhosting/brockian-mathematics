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

open Polynomial Finset

namespace Math

/-- A concrete primitive 11-th root of unity in `ℂ`. -/
noncomputable def zeta11 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11)

theorem isPrimitiveRoot_zeta11 : IsPrimitiveRoot zeta11 11 :=
  Complex.isPrimitiveRoot_exp 11 (by norm_num)

/-- The 11-th roots of unity are exactly the powers `zeta11 ^ i` for `i < 11`. -/
theorem nthRootsFinset_11_eq_image :
    nthRootsFinset 11 (1 : ℂ) = Finset.image (fun i => zeta11 ^ i) (Finset.range 11) := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Polynomial.mem_nthRootsFinset (by norm_num), ← pow_mul, mul_comm, pow_mul,
      isPrimitiveRoot_zeta11.pow_eq_one, one_pow]
  · rw [isPrimitiveRoot_zeta11.card_nthRootsFinset]
    refine le_trans (le_of_eq (by simp)) (le_of_eq (Finset.card_image_of_injOn ?_).symm)
    intro a ha b hb hab
    exact isPrimitiveRoot_zeta11.pow_inj (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab

/-- The sum of all 11-th roots of unity vanishes. -/
theorem sum_nthRootsFinset_11 : ∑ x ∈ nthRootsFinset 11 (1 : ℂ), x = 0 := by
  rw [nthRootsFinset_11_eq_image, Finset.sum_image
    (fun a ha b hb hab =>
      isPrimitiveRoot_zeta11.pow_inj (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab)]
  exact isPrimitiveRoot_zeta11.geom_sum_eq_zero (by norm_num)

/-- Since `11` is prime, every 11-th root of unity other than `1` is primitive. -/
theorem nthRootsFinset_11_eq_insert :
    nthRootsFinset 11 (1 : ℂ) = insert 1 (primitiveRoots 11 ℂ) := by
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots (R := ℂ) (n := 11)]
  have h : Nat.divisors 11 = {1, 11} := by decide
  rw [h]
  simp [IsPrimitiveRoot.primitiveRoots_one]

/-- The sum of the primitive 11-th roots of unity equals `μ 11 = -1`. -/
theorem mobius_root_sum_11 :
    ∑ ζ ∈ primitiveRoots 11 ℂ, ζ = (ArithmeticFunction.moebius 11 : ℂ) := by
  have h1 : (1 : ℂ) ∉ primitiveRoots 11 ℂ := by
    intro h
    have := (isPrimitiveRoot_of_mem_primitiveRoots h).unique IsPrimitiveRoot.one
    omega
  have hsum := sum_nthRootsFinset_11
  rw [nthRootsFinset_11_eq_insert, Finset.sum_insert h1] at hsum
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
  push_cast
  linear_combination hsum

end Math

