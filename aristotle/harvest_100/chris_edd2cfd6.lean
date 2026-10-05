/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset Complex

/-- A fixed primitive 10-th root of unity in `ℂ`. -/
noncomputable def zeta10 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

theorem isPrimitiveRoot_zeta10 : IsPrimitiveRoot zeta10 10 :=
  Complex.isPrimitiveRoot_exp 10 (by norm_num)

/-- Distinct exponents below `10` give distinct powers of `ζ`. -/
theorem zeta10_pow_ne (i j : ℕ) (hi : i < 10) (hj : j < 10) (hij : i ≠ j) :
    zeta10 ^ i ≠ zeta10 ^ j := fun hc =>
  hij (isPrimitiveRoot_zeta10.pow_inj hi hj hc)

/-- `ζ^5 = -1` for a primitive 10-th root of unity. -/
theorem zeta10_pow_five : zeta10 ^ 5 = -1 := by
  have h := isPrimitiveRoot_zeta10
  have h10 : zeta10 ^ 10 = 1 := h.pow_eq_one
  have hne : zeta10 ^ 5 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (zeta10 ^ 5 - 1) * (zeta10 ^ 5 + 1) = 0 := by linear_combination h10
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) hne
  · linear_combination h2

/-- The geometric relation coming from `ζ²` being a primitive 5-th root of unity. -/
theorem zeta10_geom :
    1 + zeta10 ^ 2 + zeta10 ^ 4 + zeta10 ^ 6 + zeta10 ^ 8 = 0 := by
  have h := isPrimitiveRoot_zeta10
  have h5 : IsPrimitiveRoot (zeta10 ^ 2) 5 := h.pow (by norm_num) (by norm_num)
  have hs := h5.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← pow_mul] at hs
  linear_combination hs

/-- The four primitive 10-th roots of unity, explicitly. -/
theorem primitiveRoots_ten_eq :
    primitiveRoots 10 ℂ = {zeta10 ^ 1, zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} := by
  have h := isPrimitiveRoot_zeta10
  have hsub : ({zeta10 ^ 1, zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} : Finset ℂ) ⊆
      primitiveRoots 10 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with rfl | rfl | rfl | rfl
    · exact h.pow_of_coprime 1 (by norm_num)
    · exact h.pow_of_coprime 3 (by norm_num)
    · exact h.pow_of_coprime 7 (by norm_num)
    · exact h.pow_of_coprime 9 (by norm_num)
  have hcard : (primitiveRoots 10 ℂ).card ≤
      ({zeta10 ^ 1, zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} : Finset ℂ).card := by
    have h1 : (primitiveRoots 10 ℂ).card = 4 := by
      rw [Complex.card_primitiveRoots]
      decide
    rw [h1, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨zeta10_pow_ne 1 3 (by norm_num) (by norm_num) (by norm_num),
          zeta10_pow_ne 1 7 (by norm_num) (by norm_num) (by norm_num),
          zeta10_pow_ne 1 9 (by norm_num) (by norm_num) (by norm_num)⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨zeta10_pow_ne 3 7 (by norm_num) (by norm_num) (by norm_num),
          zeta10_pow_ne 3 9 (by norm_num) (by norm_num) (by norm_num)⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact zeta10_pow_ne 7 9 (by norm_num) (by norm_num) (by norm_num)),
      Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- The sum of the primitive 10-th roots of unity equals `μ(10) = 1`. -/
theorem mobius_root_sum_10 :
    ∑ z ∈ primitiveRoots 10 ℂ, z = (ArithmeticFunction.moebius 10 : ℂ) := by
  have hmu : ((ArithmeticFunction.moebius 10 : ℤ) : ℂ) = 1 := by
    have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (m := 2) (n := 5) (by norm_num)
    have : (ArithmeticFunction.moebius 10 : ℤ) = 1 := by
      rw [show (10 : ℕ) = 2 * 5 by norm_num, hmul,
        ArithmeticFunction.moebius_apply_prime (by norm_num),
        ArithmeticFunction.moebius_apply_prime (by norm_num)]
      norm_num
    rw [this]; norm_num
  rw [primitiveRoots_ten_eq, hmu,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨zeta10_pow_ne 1 3 (by norm_num) (by norm_num) (by norm_num),
        zeta10_pow_ne 1 7 (by norm_num) (by norm_num) (by norm_num),
        zeta10_pow_ne 1 9 (by norm_num) (by norm_num) (by norm_num)⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨zeta10_pow_ne 3 7 (by norm_num) (by norm_num) (by norm_num),
        zeta10_pow_ne 3 9 (by norm_num) (by norm_num) (by norm_num)⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact zeta10_pow_ne 7 9 (by norm_num) (by norm_num) (by norm_num)),
    Finset.sum_singleton]
  linear_combination zeta10 * zeta10_geom - zeta10_pow_five

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

