/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open ArithmeticFunction Finset

/-- The Möbius function at `10` equals `1`. -/
lemma moebius_ten : (moebius 10 : ℤ) = 1 := by
  rw [show (10 : ℕ) = 2 * 5 from rfl,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    moebius_apply_prime Nat.prime_two, moebius_apply_prime (by norm_num)]
  norm_num

/-- A primitive `10`-th root of unity satisfies `ζ ^ 5 = -1`. -/
lemma pow_five_eq_neg_one {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) : ζ ^ 5 = -1 := by
  have h10 : ζ ^ 10 = 1 := h.pow_eq_one
  have h5 : ζ ^ 5 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (ζ ^ 5 - 1) * (ζ ^ 5 + 1) = 0 := by linear_combination h10
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact absurd (sub_eq_zero.mp h') h5
  · linear_combination h'

/-- The cyclotomic relation `ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0` for a primitive
`10`-th root of unity. -/
lemma cyclotomic_ten_eval {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 := by
  have h5 : ζ ^ 5 = -1 := pow_five_eq_neg_one h
  have hne : ζ + 1 ≠ 0 := by
    intro hc
    have hsq : ζ ^ 2 = 1 := by linear_combination (ζ - 1) * hc
    exact h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) hsq
  have hprod : (ζ + 1) * (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1) = 0 := by linear_combination h5
  exact (mul_eq_zero.mp hprod).resolve_left hne

/-- Distinct exponents below `10` give distinct powers of a primitive `10`-th root of unity. -/
lemma pow_ne_pow {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) {i j : ℕ} (hi : i < 10) (hj : j < 10)
    (hij : i ≠ j) : ζ ^ i ≠ ζ ^ j := fun hc => hij (h.pow_inj hi hj hc)

lemma notMem_one {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 1 ∉ ({ζ ^ 3, ζ ^ 7, ζ ^ 9} : Finset ℂ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨pow_ne_pow h (by norm_num) (by norm_num) (by norm_num),
    pow_ne_pow h (by norm_num) (by norm_num) (by norm_num),
    pow_ne_pow h (by norm_num) (by norm_num) (by norm_num)⟩

lemma notMem_three {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 3 ∉ ({ζ ^ 7, ζ ^ 9} : Finset ℂ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨pow_ne_pow h (by norm_num) (by norm_num) (by norm_num),
    pow_ne_pow h (by norm_num) (by norm_num) (by norm_num)⟩

lemma notMem_seven {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 7 ∉ ({ζ ^ 9} : Finset ℂ) := by
  simp only [Finset.mem_singleton]
  exact pow_ne_pow h (by norm_num) (by norm_num) (by norm_num)

/-- The set of primitive `10`-th roots of unity in `ℂ` is `{ζ, ζ ^ 3, ζ ^ 7, ζ ^ 9}`. -/
lemma primitiveRoots_ten_eq {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    primitiveRoots 10 ℂ = {ζ ^ 1, ζ ^ 3, ζ ^ 7, ζ ^ 9} := by
  have hsub : ({ζ ^ 1, ζ ^ 3, ζ ^ 7, ζ ^ 9} : Finset ℂ) ⊆ primitiveRoots 10 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with rfl | rfl | rfl | rfl
    · exact h.pow_of_coprime 1 (by norm_num)
    · exact h.pow_of_coprime 3 (by norm_num)
    · exact h.pow_of_coprime 7 (by norm_num)
    · exact h.pow_of_coprime 9 (by norm_num)
  have hcard : ({ζ ^ 1, ζ ^ 3, ζ ^ 7, ζ ^ 9} : Finset ℂ).card = 4 := by
    rw [Finset.card_insert_of_notMem (notMem_one h), Finset.card_insert_of_notMem (notMem_three h),
        Finset.card_insert_of_notMem (notMem_seven h), Finset.card_singleton]
  have hcard' : (primitiveRoots 10 ℂ).card = 4 := by
    rw [Complex.card_primitiveRoots]
    decide
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard'])).symm

/-- **Möbius root sum for `n = 10`**: the sum of the primitive `10`-th roots of unity
in `ℂ` equals `μ(10) = 1`. -/
theorem mobius_root_sum_10 :
    ∑ z ∈ primitiveRoots 10 ℂ, z = (moebius 10 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 10 :=
    ⟨_, Complex.isPrimitiveRoot_exp 10 (by norm_num)⟩
  have hmu : ((moebius 10 : ℤ) : ℂ) = 1 := by rw [moebius_ten]; norm_num
  have h5 : ζ ^ 5 = -1 := pow_five_eq_neg_one hζ
  have hcyc : ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 := cyclotomic_ten_eval hζ
  rw [primitiveRoots_ten_eq hζ, hmu, Finset.sum_insert (notMem_one hζ),
    Finset.sum_insert (notMem_three hζ), Finset.sum_insert (notMem_seven hζ),
    Finset.sum_singleton]
  linear_combination (ζ ^ 2 + ζ ^ 4) * h5 - hcyc

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

