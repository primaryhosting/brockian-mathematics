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

open Complex ArithmeticFunction

/-- The Möbius function at `10` equals `1`. -/

theorem mobius_root_sum_10 :
    ∑ z ∈ primitiveRoots 10 ℂ, z = (moebius 10 : ℂ) := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10) with hζ
  have h : IsPrimitiveRoot ζ 10 := Complex.isPrimitiveRoot_exp 10 (by norm_num)
  have hd : ∀ i j : ℕ, i < 10 → j < 10 → i ≠ j → ζ ^ i ≠ ζ ^ j := by
    intro i j hi hj hij e
    exact hij (h.pow_inj hi hj e)
  rw [primitiveRoots_ten_eq h]
  rw [Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hd 1 3 (by norm_num) (by norm_num) (by norm_num),
        hd 1 7 (by norm_num) (by norm_num) (by norm_num),
        hd 1 9 (by norm_num) (by norm_num) (by norm_num)⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hd 3 7 (by norm_num) (by norm_num) (by norm_num),
        hd 3 9 (by norm_num) (by norm_num) (by norm_num)⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact hd 7 9 (by norm_num) (by norm_num) (by norm_num)),
    Finset.sum_singleton, moebius_ten]
  have := sum_four_powers h
  push_cast
  linear_combination this

end Math

