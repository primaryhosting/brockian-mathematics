/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Statement: The sum of the primitive 10-th roots of unity equals μ(10).
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

namespace Math

/-- A fixed primitive 10-th root of unity in `ℂ`. -/
noncomputable def zeta10 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

theorem isPrimitiveRoot_zeta10 : IsPrimitiveRoot zeta10 10 :=
  Complex.isPrimitiveRoot_exp 10 (by norm_num)

theorem zeta10_pow_five : zeta10 ^ 5 = -1 := by
  have h10 : zeta10 ^ 10 = 1 := isPrimitiveRoot_zeta10.pow_eq_one
  have h5 : zeta10 ^ 5 ≠ 1 :=
    isPrimitiveRoot_zeta10.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h : (zeta10 ^ 5 - 1) * (zeta10 ^ 5 + 1) = 0 := by linear_combination h10
  rcases mul_eq_zero.1 h with h' | h'
  · exact absurd (by linear_combination h') h5
  · linear_combination h'

/-- The four primitive 10-th roots of unity sum to `1`. -/
theorem zeta10_sum_eq_one : zeta10 + zeta10 ^ 3 + zeta10 ^ 7 + zeta10 ^ 9 = 1 := by
  have h5 : zeta10 ^ 5 = -1 := zeta10_pow_five
  have hne : zeta10 + 1 ≠ 0 := by
    intro h
    have hm : zeta10 = -1 := by linear_combination h
    have h2 : zeta10 ^ 2 = 1 := by rw [hm]; ring
    exact isPrimitiveRoot_zeta10.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h2
  have key : zeta10 ^ 4 - zeta10 ^ 3 + zeta10 ^ 2 - zeta10 + 1 = 0 := by
    have hp : (zeta10 + 1) * (zeta10 ^ 4 - zeta10 ^ 3 + zeta10 ^ 2 - zeta10 + 1) = 0 := by
      linear_combination h5
    rcases mul_eq_zero.1 hp with h | h
    · exact absurd h hne
    · exact h
  have h7 : zeta10 ^ 7 = -zeta10 ^ 2 := by
    have h : zeta10 ^ 7 = zeta10 ^ 5 * zeta10 ^ 2 := by ring
    rw [h, h5]; ring
  have h9 : zeta10 ^ 9 = -zeta10 ^ 4 := by
    have h : zeta10 ^ 9 = zeta10 ^ 5 * zeta10 ^ 4 := by ring
    rw [h, h5]; ring
  rw [h7, h9]; linear_combination -key

theorem zeta10_pow_ne {i j : ℕ} (hi : i < 10) (hj : j < 10) (hij : i ≠ j) :
    zeta10 ^ i ≠ zeta10 ^ j := fun h => hij (isPrimitiveRoot_zeta10.pow_inj hi hj h)

theorem zeta10_notMem_one : zeta10 ∉ ({zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} : Finset ℂ) := by
  have h13 : zeta10 ≠ zeta10 ^ 3 := by
    simpa using zeta10_pow_ne (i := 1) (j := 3) (by norm_num) (by norm_num) (by norm_num)
  have h17 : zeta10 ≠ zeta10 ^ 7 := by
    simpa using zeta10_pow_ne (i := 1) (j := 7) (by norm_num) (by norm_num) (by norm_num)
  have h19 : zeta10 ≠ zeta10 ^ 9 := by
    simpa using zeta10_pow_ne (i := 1) (j := 9) (by norm_num) (by norm_num) (by norm_num)
  simp [h13, h17, h19]

theorem zeta10_notMem_three : zeta10 ^ 3 ∉ ({zeta10 ^ 7, zeta10 ^ 9} : Finset ℂ) := by
  have h37 : zeta10 ^ 3 ≠ zeta10 ^ 7 :=
    zeta10_pow_ne (by norm_num) (by norm_num) (by norm_num)
  have h39 : zeta10 ^ 3 ≠ zeta10 ^ 9 :=
    zeta10_pow_ne (by norm_num) (by norm_num) (by norm_num)
  simp [h37, h39]

theorem zeta10_notMem_seven : zeta10 ^ 7 ∉ ({zeta10 ^ 9} : Finset ℂ) := by
  have h79 : zeta10 ^ 7 ≠ zeta10 ^ 9 :=
    zeta10_pow_ne (by norm_num) (by norm_num) (by norm_num)
  simp [h79]

/-- The finset of primitive 10-th roots of unity in `ℂ`, explicitly. -/
theorem primitiveRoots_ten :
    primitiveRoots 10 ℂ = {zeta10, zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} := by
  have hcard : ({zeta10, zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} : Finset ℂ).card = 4 := by
    rw [Finset.card_insert_of_notMem zeta10_notMem_one,
      Finset.card_insert_of_notMem zeta10_notMem_three,
      Finset.card_insert_of_notMem zeta10_notMem_seven, Finset.card_singleton]
  have hsub : ({zeta10, zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} : Finset ℂ) ⊆ primitiveRoots 10 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with rfl | rfl | rfl | rfl
    · exact isPrimitiveRoot_zeta10
    · exact isPrimitiveRoot_zeta10.pow_of_coprime 3 (by norm_num)
    · exact isPrimitiveRoot_zeta10.pow_of_coprime 7 (by norm_num)
    · exact isPrimitiveRoot_zeta10.pow_of_coprime 9 (by norm_num)
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Complex.card_primitiveRoots, hcard, show Nat.totient 10 = 4 from by decide]

theorem moebius_ten : ArithmeticFunction.moebius 10 = 1 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num)]
  simp [ArithmeticFunction.moebius_apply_prime, Nat.prime_two, (by norm_num : Nat.Prime 5)]

/-- The sum of the primitive 10-th roots of unity in `ℂ` equals `μ(10)`. -/
theorem mobius_root_sum_10 :
    ∑ z ∈ primitiveRoots 10 ℂ, z = ((ArithmeticFunction.moebius 10 : ℤ) : ℂ) := by
  rw [primitiveRoots_ten, moebius_ten,
    Finset.sum_insert zeta10_notMem_one,
    Finset.sum_insert zeta10_notMem_three,
    Finset.sum_insert zeta10_notMem_seven, Finset.sum_singleton]
  push_cast
  linear_combination zeta10_sum_eq_one

end Math

