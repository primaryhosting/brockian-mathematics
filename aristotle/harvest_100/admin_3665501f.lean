import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- `μ 10 = 1`, since `10 = 2 * 5` is a product of two distinct primes. -/
lemma moebius_ten : ArithmeticFunction.moebius 10 = 1 := by
  have h : (10 : ℕ) = 2 * 5 := by norm_num
  rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

/-- A primitive `10`-th root of unity `z` satisfies `z ^ 5 = -1`. -/
lemma pow_five_eq_neg_one {z : ℂ} (hz : IsPrimitiveRoot z 10) : z ^ 5 = -1 := by
  have h1 : z ^ 5 * z ^ 5 = 1 := by
    rw [← pow_add]; exact hz.pow_eq_one
  have h2 : z ^ 5 ≠ 1 := fun h => by
    have := Nat.le_of_dvd (by norm_num) (hz.dvd_of_pow_eq_one 5 h)
    omega
  exact (mul_self_eq_one_iff.mp h1).resolve_left h2

/-- A primitive `10`-th root of unity is a root of the tenth cyclotomic polynomial
`X ^ 4 - X ^ 3 + X ^ 2 - X + 1`. -/
lemma cyclotomic_ten_eval {z : ℂ} (hz : IsPrimitiveRoot z 10) :
    z ^ 4 - z ^ 3 + z ^ 2 - z + 1 = 0 := by
  have h5 : z ^ 5 = -1 := pow_five_eq_neg_one hz
  have hzne : z ≠ -1 := by
    intro h
    have h2 : z ^ 2 = 1 := by rw [h]; ring
    have := Nat.le_of_dvd (by norm_num) (hz.dvd_of_pow_eq_one 2 h2)
    omega
  have hne : z + 1 ≠ 0 := fun h => hzne (by linear_combination h)
  have key : (z + 1) * (z ^ 4 - z ^ 3 + z ^ 2 - z + 1) = 0 := by linear_combination h5
  exact (mul_eq_zero.mp key).resolve_left hne

/-- Given a primitive `10`-th root of unity `z`, the four primitive `10`-th roots of unity
are `z, z ^ 3, z ^ 7, z ^ 9`. -/
lemma primitiveRoots_ten_eq {z : ℂ} (hz : IsPrimitiveRoot z 10) :
    primitiveRoots 10 ℂ = {z, z ^ 3, z ^ 7, z ^ 9} := by
  have hinj : ∀ i j : ℕ, i < 10 → j < 10 → z ^ i = z ^ j → i = j := fun i j hi hj h =>
    hz.pow_inj hi hj h
  have d13 : z ≠ z ^ 3 := fun h => by
    have := hinj 1 3 (by norm_num) (by norm_num) (by simpa using h); omega
  have d17 : z ≠ z ^ 7 := fun h => by
    have := hinj 1 7 (by norm_num) (by norm_num) (by simpa using h); omega
  have d19 : z ≠ z ^ 9 := fun h => by
    have := hinj 1 9 (by norm_num) (by norm_num) (by simpa using h); omega
  have d37 : z ^ 3 ≠ z ^ 7 := fun h => by
    have := hinj 3 7 (by norm_num) (by norm_num) h; omega
  have d39 : z ^ 3 ≠ z ^ 9 := fun h => by
    have := hinj 3 9 (by norm_num) (by norm_num) h; omega
  have d79 : z ^ 7 ≠ z ^ 9 := fun h => by
    have := hinj 7 9 (by norm_num) (by norm_num) h; omega
  have hcard : ({z, z ^ 3, z ^ 7, z ^ 9} : Finset ℂ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [d13, d17, d19]),
      Finset.card_insert_of_notMem (by simp [d37, d39]),
      Finset.card_insert_of_notMem (by simp [d79]), Finset.card_singleton]
  have hsub : ({z, z ^ 3, z ^ 7, z ^ 9} : Finset ℂ) ⊆ primitiveRoots 10 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with rfl | rfl | rfl | rfl
    · exact hz
    · exact hz.pow_of_coprime 3 (by norm_num)
    · exact hz.pow_of_coprime 7 (by norm_num)
    · exact hz.pow_of_coprime 9 (by norm_num)
  have hcard' : (primitiveRoots 10 ℂ).card = 4 := by
    rw [hz.card_primitiveRoots]
    decide
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard'])).symm

/-- **The sum of the primitive 10-th roots of unity equals `μ(10)`.** -/
theorem mobius_root_sum_10 :
    ∑ z ∈ primitiveRoots 10 ℂ, z = (ArithmeticFunction.moebius 10 : ℂ) := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, IsPrimitiveRoot z 10 :=
    ⟨_, Complex.isPrimitiveRoot_exp 10 (by norm_num)⟩
  have hinj : ∀ i j : ℕ, i < 10 → j < 10 → z ^ i = z ^ j → i = j := fun i j hi hj h =>
    hz.pow_inj hi hj h
  have d13 : z ≠ z ^ 3 := fun h => by
    have := hinj 1 3 (by norm_num) (by norm_num) (by simpa using h); omega
  have d17 : z ≠ z ^ 7 := fun h => by
    have := hinj 1 7 (by norm_num) (by norm_num) (by simpa using h); omega
  have d19 : z ≠ z ^ 9 := fun h => by
    have := hinj 1 9 (by norm_num) (by norm_num) (by simpa using h); omega
  have d37 : z ^ 3 ≠ z ^ 7 := fun h => by
    have := hinj 3 7 (by norm_num) (by norm_num) h; omega
  have d39 : z ^ 3 ≠ z ^ 9 := fun h => by
    have := hinj 3 9 (by norm_num) (by norm_num) h; omega
  have d79 : z ^ 7 ≠ z ^ 9 := fun h => by
    have := hinj 7 9 (by norm_num) (by norm_num) h; omega
  rw [primitiveRoots_ten_eq hz, Finset.sum_insert (by simp [d13, d17, d19]),
    Finset.sum_insert (by simp [d37, d39]), Finset.sum_insert (by simp [d79]),
    Finset.sum_singleton, moebius_ten]
  have h5 : z ^ 5 = -1 := pow_five_eq_neg_one hz
  have hc : z ^ 4 - z ^ 3 + z ^ 2 - z + 1 = 0 := cyclotomic_ten_eval hz
  push_cast
  linear_combination (z ^ 2 + z ^ 4) * h5 - hc

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

