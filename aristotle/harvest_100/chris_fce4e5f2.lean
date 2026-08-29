/-
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A fixed primitive cube root of unity in `ℂ`. -/
noncomputable def zeta3 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

lemma isPrimitiveRoot_zeta3 : IsPrimitiveRoot zeta3 3 := by
  have := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [zeta3, mul_comm, mul_assoc, mul_left_comm] using this

lemma zeta3_sq_add_zeta3_add_one : zeta3 ^ 2 + zeta3 + 1 = 0 := by
  have h1 : zeta3 ^ 3 = 1 := isPrimitiveRoot_zeta3.pow_eq_one
  have h2 : zeta3 ≠ 1 := by
    intro h
    have := isPrimitiveRoot_zeta3
    rw [h] at this
    have := this.unique (IsPrimitiveRoot.one)
    omega
  have h3 : (zeta3 - 1) * (zeta3 ^ 2 + zeta3 + 1) = 0 := by ring_nf; linear_combination h1
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact h

lemma zeta3_ne_sq : zeta3 ≠ zeta3 ^ 2 := by
  intro h
  have hz := isPrimitiveRoot_zeta3
  have hz0 : zeta3 ≠ 0 := by
    intro h0
    have := hz.pow_eq_one
    rw [h0] at this
    norm_num at this
  have hmul : zeta3 * (zeta3 - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 hmul with h' | h'
  · exact hz0 h'
  · rw [sub_eq_zero.1 h'] at hz
    have := hz.unique (IsPrimitiveRoot.one)
    omega

lemma primitiveRoots_three : primitiveRoots 3 ℂ = {zeta3, zeta3 ^ 2} := by
  have hz := isPrimitiveRoot_zeta3
  have hz2 : IsPrimitiveRoot (zeta3 ^ 2) 3 := hz.pow_of_coprime 2 (by decide)
  have hsub : ({zeta3, zeta3 ^ 2} : Finset ℂ) ⊆ primitiveRoots 3 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 hz
    · exact (mem_primitiveRoots (by norm_num)).2 hz2
  have hcard : (primitiveRoots 3 ℂ).card = 2 := by
    rw [hz.card_primitiveRoots]
    decide
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, Finset.card_insert_of_notMem (by simpa using zeta3_ne_sq), Finset.card_singleton]

/-- The sum of the primitive cube roots of unity equals `μ(3) = -1`. -/
theorem mobius_root_sum_3 :
    ∑ ζ ∈ primitiveRoots 3 ℂ, ζ = (ArithmeticFunction.moebius 3 : ℤ) := by
  rw [primitiveRoots_three, Finset.sum_insert (by simpa using zeta3_ne_sq),
    Finset.sum_singleton, ArithmeticFunction.moebius_apply_prime (by norm_num)]
  push_cast
  linear_combination zeta3_sq_add_zeta3_add_one

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

