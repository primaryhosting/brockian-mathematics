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

open Finset

namespace Math

/-- The Möbius function at `6` equals `1` (since `6 = 2 * 3` is squarefree with two prime
factors). -/
theorem moebius_six : ArithmeticFunction.moebius 6 = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (by decide +kernel),
    ArithmeticFunction.cardFactors_apply,
    show Nat.primeFactorsList 6 = [2, 3] from by decide +kernel]
  norm_num

/-- A primitive `6`-th root of unity in `ℂ` is a root of the sixth cyclotomic polynomial
`X ^ 2 - X + 1`. -/
theorem cyclotomic_six_eq_zero_of_isPrimitiveRoot {z : ℂ} (h : IsPrimitiveRoot z 6) :
    z ^ 2 - z + 1 = 0 := by
  have h6 : z ^ 6 = 1 := h.pow_eq_one
  have h2 : z ^ 2 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h3 : z ^ 3 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have key : (z ^ 2 - 1) * (z ^ 2 + z + 1) * (z ^ 2 - z + 1) = 0 := by
    linear_combination h6
  rcases mul_eq_zero.1 key with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · exact absurd (by linear_combination h'' : z ^ 2 = 1) h2
    · exact absurd (by linear_combination (z - 1) * h'' : z ^ 3 = 1) h3
  · exact h'

/-- The set of primitive `6`-th roots of unity in `ℂ` consists of exactly `z` and `z ^ 5`,
for any primitive `6`-th root of unity `z`. -/
theorem primitiveRoots_six_eq {z : ℂ} (h : IsPrimitiveRoot z 6) :
    primitiveRoots 6 ℂ = {z, z ^ 5} := by
  have hz2 : z ^ 2 - z + 1 = 0 := cyclotomic_six_eq_zero_of_isPrimitiveRoot h
  have hne : z ≠ z ^ 5 := by
    intro he
    have h1 : 2 * z - 1 = 0 := by linear_combination he + (z ^ 3 + z ^ 2 - 1) * hz2
    have h3 : (3 : ℂ) = 0 := by linear_combination 4 * hz2 - (2 * z - 1) * h1
    norm_num at h3
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 h
    · exact (mem_primitiveRoots (by norm_num)).2 (h.pow_of_coprime 5 (by norm_num))
  · rw [h.card_primitiveRoots, show Nat.totient 6 = 2 from by decide +kernel,
      Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- **The sum of the primitive 6-th roots of unity equals `μ(6)`.** -/
theorem mobius_root_sum_6 :
    ∑ z ∈ primitiveRoots 6 ℂ, z = (ArithmeticFunction.moebius 6 : ℂ) := by
  have h : IsPrimitiveRoot (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 6)) 6 :=
    Complex.isPrimitiveRoot_exp 6 (by norm_num)
  set z := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 6)
  have hz2 : z ^ 2 - z + 1 = 0 := cyclotomic_six_eq_zero_of_isPrimitiveRoot h
  have hne : z ≠ z ^ 5 := by
    intro he
    have h1 : 2 * z - 1 = 0 := by linear_combination he + (z ^ 3 + z ^ 2 - 1) * hz2
    have h3 : (3 : ℂ) = 0 := by linear_combination 4 * hz2 - (2 * z - 1) * h1
    norm_num at h3
  rw [primitiveRoots_six_eq h, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    moebius_six]
  push_cast
  linear_combination (z ^ 3 + z ^ 2 - 1) * hz2

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

