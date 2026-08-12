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

/-- The sum of the primitive `6`-th roots of unity in `ℂ` equals `μ 6`, the Möbius
function evaluated at `6` (which is `1`). -/
theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = (ArithmeticFunction.moebius 6 : ℂ) := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 6) with hζdef
  have h : IsPrimitiveRoot ζ 6 := by
    have := Complex.isPrimitiveRoot_exp 6 (by norm_num)
    simpa [hζdef] using this
  have h6 : ζ ^ 6 = 1 := h.pow_eq_one
  have hz : ζ ≠ 0 := by
    intro h0
    rw [h0] at h6; norm_num at h6
  -- `ζ ^ 3` squares to `1` and is not `1`, hence equals `-1`
  have h3 : ζ ^ 3 = -1 := by
    have hne : ζ ^ 3 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have hfac : (ζ ^ 3 - 1) * (ζ ^ 3 + 1) = 0 := by linear_combination h6
    rcases mul_eq_zero.1 hfac with h' | h'
    · exact absurd (by linear_combination h') hne
    · linear_combination h'
  -- `ζ ^ 2` is a primitive cube root of unity
  have h2 : IsPrimitiveRoot (ζ ^ 2) 3 := h.pow (by norm_num) (by norm_num)
  have hsum3 : (1 : ℂ) + ζ ^ 2 + ζ ^ 4 = 0 := by
    have := h2.geom_sum_eq_zero (by norm_num)
    simp [Finset.sum_range_succ] at this
    linear_combination this
  have key : ζ + ζ ^ 5 = 1 := by
    linear_combination -hsum3 + (ζ + ζ ^ 2) * h3
  have hsub : ({ζ, ζ ^ 5} : Finset ℂ) ⊆ primitiveRoots 6 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 h
    · exact (mem_primitiveRoots (by norm_num)).2 (h.pow_of_coprime 5 (by norm_num))
  have hne5 : ζ ≠ ζ ^ 5 := by
    intro hcon
    have h4 : ζ ^ 4 = 1 := by
      have hmul : ζ * ζ ^ 4 = ζ * 1 := by rw [mul_one]; linear_combination -hcon
      exact mul_left_cancel₀ hz hmul
    exact h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h4
  have hcard : ({ζ, ζ ^ 5} : Finset ℂ).card = (primitiveRoots 6 ℂ).card := by
    rw [Complex.card_primitiveRoots, Finset.card_insert_of_notMem (by simpa using hne5)]
    norm_num
    decide +kernel
  have heq : primitiveRoots 6 ℂ = ({ζ, ζ ^ 5} : Finset ℂ) :=
    (Finset.eq_of_subset_of_card_le hsub hcard.ge).symm
  rw [heq, Finset.sum_insert (by simpa using hne5), Finset.sum_singleton, key]
  have hmu : (ArithmeticFunction.moebius 6 : ℤ) = 1 := by
    have h63 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h63, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.moebius_apply_prime (by norm_num),
      ArithmeticFunction.moebius_apply_prime (by norm_num)]
    norm_num
  rw [hmu]
  norm_num

end Math

