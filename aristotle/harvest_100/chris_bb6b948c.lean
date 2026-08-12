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
lemma moebius_ten : moebius 10 = 1 := by
  have h2 : (10 : ℕ) = 2 * 5 := by norm_num
  rw [h2, isMultiplicative_moebius.map_mul_of_coprime (by norm_num)]
  rw [moebius_apply_prime Nat.prime_two, moebius_apply_prime (by norm_num)]
  norm_num

/-- A primitive `10`-th root of unity satisfies `ζ ^ 5 = -1`. -/
lemma pow_five_eq_neg_one {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) : ζ ^ 5 = -1 := by
  have h10 : (ζ ^ 5) ^ 2 = 1 := by
    rw [← pow_mul]; exact h.pow_eq_one
  have hne : ζ ^ 5 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  rcases mul_eq_zero.1 (show (ζ ^ 5 - 1) * (ζ ^ 5 + 1) = 0 by linear_combination h10) with h1 | h1
  · exact absurd (by linear_combination h1) hne
  · linear_combination h1

/-- The four primitive `10`-th roots of unity sum to `1`. -/
lemma sum_four_powers {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 1 + ζ ^ 3 + ζ ^ 7 + ζ ^ 9 = 1 := by
  have h5 : ζ ^ 5 = -1 := pow_five_eq_neg_one h
  have hne : ζ + 1 ≠ 0 := by
    intro hz
    have hz' : ζ = -1 := by linear_combination hz
    have := h.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num)
    apply this
    rw [hz']; norm_num
  have key : (ζ + 1) * (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1) = 0 := by
    linear_combination h5
  have h4 : ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 :=
    (mul_eq_zero.1 key).resolve_left hne
  have h7 : ζ ^ 7 = -ζ ^ 2 := by
    have : ζ ^ 7 = ζ ^ 5 * ζ ^ 2 := by ring
    rw [this, h5]; ring
  have h9 : ζ ^ 9 = -ζ ^ 4 := by
    have : ζ ^ 9 = ζ ^ 5 * ζ ^ 4 := by ring
    rw [this, h5]; ring
  rw [h7, h9]
  linear_combination -h4

/-- The set of primitive `10`-th roots of unity in `ℂ`, described explicitly in terms of
one of them. -/
lemma primitiveRoots_ten_eq {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    primitiveRoots 10 ℂ = {ζ ^ 1, ζ ^ 3, ζ ^ 7, ζ ^ 9} := by
  have hd : ∀ i j : ℕ, i < 10 → j < 10 → i ≠ j → ζ ^ i ≠ ζ ^ j := by
    intro i j hi hj hij e
    exact hij (h.pow_inj hi hj e)
  have hsub : ({ζ ^ 1, ζ ^ 3, ζ ^ 7, ζ ^ 9} : Finset ℂ) ⊆ primitiveRoots 10 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with rfl | rfl | rfl | rfl
    · exact h.pow_of_coprime 1 (by norm_num)
    · exact h.pow_of_coprime 3 (by decide)
    · exact h.pow_of_coprime 7 (by decide)
    · exact h.pow_of_coprime 9 (by decide)
  have hcard : ({ζ ^ 1, ζ ^ 3, ζ ^ 7, ζ ^ 9} : Finset ℂ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨hd 1 3 (by norm_num) (by norm_num) (by norm_num),
          hd 1 7 (by norm_num) (by norm_num) (by norm_num),
          hd 1 9 (by norm_num) (by norm_num) (by norm_num)⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨hd 3 7 (by norm_num) (by norm_num) (by norm_num),
          hd 3 9 (by norm_num) (by norm_num) (by norm_num)⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact hd 7 9 (by norm_num) (by norm_num) (by norm_num)),
      Finset.card_singleton]
  have hc : (primitiveRoots 10 ℂ).card = 4 := by
    rw [Complex.card_primitiveRoots]
    decide
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hc])).symm

/-- **The sum of the primitive 10-th roots of unity equals `μ(10)`.** -/
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

