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

/-
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- With `ζ = exp(2πi/5)`, the finset of primitive 5-th roots of unity in `ℂ`
is exactly `{ζ, ζ², ζ³, ζ⁴}`. -/
theorem primitiveRoots_five_eq (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) :
    primitiveRoots 5 ℂ = ({ζ, ζ ^ 2, ζ ^ 3, ζ ^ 4} : Finset ℂ) := by
  have hpow : ∀ i : ℕ, 0 < i → i < 5 → ζ ^ i ∈ primitiveRoots 5 ℂ := by
    intro i hi hi5
    refine (mem_primitiveRoots (by norm_num)).2 (hζ.pow_of_coprime i ?_)
    interval_cases i <;> decide
  have hinj : ∀ i j : ℕ, i < 5 → j < 5 → ζ ^ i = ζ ^ j → i = j := by
    intro i j hi hj h
    exact hζ.pow_inj hi hj h
  have hsub : ({ζ, ζ ^ 2, ζ ^ 3, ζ ^ 4} : Finset ℂ) ⊆ primitiveRoots 5 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa using hpow 1 (by norm_num) (by norm_num)
    · exact hpow 2 (by norm_num) (by norm_num)
    · exact hpow 3 (by norm_num) (by norm_num)
    · exact hpow 4 (by norm_num) (by norm_num)
  have hcard : #({ζ, ζ ^ 2, ζ ^ 3, ζ ^ 4} : Finset ℂ) = 4 := by
    have h12 : ζ ≠ ζ ^ 2 := fun h => by
      have := hinj 1 2 (by norm_num) (by norm_num) (by simpa using h); omega
    have h13 : ζ ≠ ζ ^ 3 := fun h => by
      have := hinj 1 3 (by norm_num) (by norm_num) (by simpa using h); omega
    have h14 : ζ ≠ ζ ^ 4 := fun h => by
      have := hinj 1 4 (by norm_num) (by norm_num) (by simpa using h); omega
    have h23 : ζ ^ 2 ≠ ζ ^ 3 := fun h => by
      have := hinj 2 3 (by norm_num) (by norm_num) h; omega
    have h24 : ζ ^ 2 ≠ ζ ^ 4 := fun h => by
      have := hinj 2 4 (by norm_num) (by norm_num) h; omega
    have h34 : ζ ^ 3 ≠ ζ ^ 4 := fun h => by
      have := hinj 3 4 (by norm_num) (by norm_num) h; omega
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_insert_of_notMem (by simp [h23, h24]),
      Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, Complex.card_primitiveRoots]
  decide

/-- The sum of the primitive 5-th roots of unity in `ℂ` equals `μ(5) = -1`. -/
theorem mobius_root_sum_5 :
    ∑ z ∈ primitiveRoots 5 ℂ, z = (ArithmeticFunction.moebius 5 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 5 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 5), Complex.isPrimitiveRoot_exp 5 (by norm_num)⟩
  have hgeom : ∑ i ∈ Finset.range 5, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hmu : (ArithmeticFunction.moebius 5 : ℂ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
    norm_num
  rw [primitiveRoots_five_eq ζ hζ, hmu]
  have hinj : ∀ i j : ℕ, i < 5 → j < 5 → ζ ^ i = ζ ^ j → i = j :=
    fun i j hi hj h => hζ.pow_inj hi hj h
  have h12 : ζ ≠ ζ ^ 2 := fun h => by
    have := hinj 1 2 (by norm_num) (by norm_num) (by simpa using h); omega
  have h13 : ζ ≠ ζ ^ 3 := fun h => by
    have := hinj 1 3 (by norm_num) (by norm_num) (by simpa using h); omega
  have h14 : ζ ≠ ζ ^ 4 := fun h => by
    have := hinj 1 4 (by norm_num) (by norm_num) (by simpa using h); omega
  have h23 : ζ ^ 2 ≠ ζ ^ 3 := fun h => by
    have := hinj 2 3 (by norm_num) (by norm_num) h; omega
  have h24 : ζ ^ 2 ≠ ζ ^ 4 := fun h => by
    have := hinj 2 4 (by norm_num) (by norm_num) h; omega
  have h34 : ζ ^ 3 ≠ ζ ^ 4 := fun h => by
    have := hinj 3 4 (by norm_num) (by norm_num) h; omega
  rw [Finset.sum_insert (by simp [h12, h13, h14]),
    Finset.sum_insert (by simp [h23, h24]),
    Finset.sum_insert (by simp [h34]), Finset.sum_singleton]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at hgeom
  linear_combination hgeom

end Math

