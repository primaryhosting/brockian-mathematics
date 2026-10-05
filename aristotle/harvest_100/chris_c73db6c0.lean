/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped ArithmeticFunction.Moebius

namespace Math

/-- The set of primitive `6`-th roots of unity in `ℂ` is `{ζ, ζ ^ 5}` for any
primitive sixth root of unity `ζ`. -/
lemma primitiveRoots_six_eq (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 6) :
    primitiveRoots 6 ℂ = {ζ, ζ ^ 5} := by
  have hne : ζ ≠ ζ ^ 5 := by
    intro h
    have h1 : ζ ^ 1 = ζ ^ 5 := by simpa using h
    have := hζ.pow_inj (by norm_num) (by norm_num) h1
    omega
  have h5 : IsPrimitiveRoot (ζ ^ 5) 6 := hζ.pow_of_coprime 5 (by decide)
  have hsub : ({ζ, ζ ^ 5} : Finset ℂ) ⊆ primitiveRoots 6 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 hζ
    · exact (mem_primitiveRoots (by norm_num)).2 h5
  have hcard : (primitiveRoots 6 ℂ).card = 2 := by
    rw [hζ.card_primitiveRoots]
    decide
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- Any primitive sixth root of unity satisfies the sixth cyclotomic equation
`ζ ^ 2 - ζ + 1 = 0`. -/
lemma sq_sub_self_add_one_eq_zero (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 6) :
    ζ ^ 2 - ζ + 1 = 0 := by
  have h6 : ζ ^ 6 = 1 := hζ.pow_eq_one
  have h3 : ζ ^ 3 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h1 : ζ ^ 3 = -1 := by
    have hfac : (ζ ^ 3 - 1) * (ζ ^ 3 + 1) = 0 := by linear_combination h6
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) h3
    · exact eq_neg_of_add_eq_zero_left h
  have h2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hm1 : ζ ≠ -1 := by
    intro h
    exact h2 (by rw [h]; norm_num)
  have hfac : (ζ + 1) * (ζ ^ 2 - ζ + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (eq_neg_of_add_eq_zero_left h) hm1
  · exact h

/-- The sum of the primitive `6`-th roots of unity equals `μ(6) = 1`. -/
theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = ((μ 6 : ℤ) : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 6 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 6), Complex.isPrimitiveRoot_exp 6 (by norm_num)⟩
  have hne : ζ ≠ ζ ^ 5 := by
    intro h
    have h1 : ζ ^ 1 = ζ ^ 5 := by simpa using h
    have := hζ.pow_inj (by norm_num) (by norm_num) h1
    omega
  rw [primitiveRoots_six_eq ζ hζ, Finset.sum_pair hne]
  have hq := sq_sub_self_add_one_eq_zero ζ hζ
  have hmu : (μ 6 : ℤ) = 1 := by
    have h : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.moebius_apply_prime (by norm_num),
      ArithmeticFunction.moebius_apply_prime (by norm_num)]
    norm_num
  rw [hmu]
  push_cast
  linear_combination (ζ ^ 3 + ζ ^ 2 - 1) * hq

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

