/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Complex

namespace Math

/-- The two primitive 6-th roots of unity, written explicitly. -/
private noncomputable def zA : ℂ := (1 + Complex.I * (Real.sqrt 3 : ℝ)) / 2
private noncomputable def zB : ℂ := (1 - Complex.I * (Real.sqrt 3 : ℝ)) / 2

private lemma sq_sqrt_three : (((Real.sqrt 3 : ℝ) : ℂ)) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
  norm_num

/-- A complex number is a primitive 6-th root of unity iff it is a root of `X ^ 2 - X + 1`. -/
private lemma isPrimitiveRoot_six_iff (z : ℂ) :
    IsPrimitiveRoot z 6 ↔ z ^ 2 - z + 1 = 0 := by
  constructor
  · intro h
    have h6 : z ^ 6 = 1 := h.pow_eq_one
    have hfac : (z ^ 2 - z + 1) * ((z ^ 2 + z + 1) * (z ^ 2 - 1)) = 0 := by
      linear_combination h6
    rcases mul_eq_zero.1 hfac with h1 | h2
    · exact h1
    · rcases mul_eq_zero.1 h2 with ha | hb
      · exact absurd (show z ^ 3 = 1 by linear_combination (z - 1) * ha)
          (h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
      · exact absurd (show z ^ 2 = 1 by linear_combination hb)
          (h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  · intro h
    have h3 : z ^ 3 = -1 := by linear_combination (z + 1) * h
    refine IsPrimitiveRoot.mk_of_lt z (by norm_num) (by linear_combination (z ^ 3 - 1) * h3)
      (fun l hl0 hl6 hl => ?_)
    interval_cases l
    · rw [pow_one] at hl
      rw [hl] at h; norm_num at h
    · have hz : z = 2 := by linear_combination hl - h
      rw [hz] at h; norm_num at h
    · rw [h3] at hl; norm_num at hl
    · have hz : z = -1 := by linear_combination z * h3 - hl
      rw [hz] at h; norm_num at h
    · have hz : z = 0 := by linear_combination (-1 : ℂ) * h - hl + z ^ 2 * h3
      rw [hz] at h; norm_num at h

private lemma zA_ne_zB : zA ≠ zB := by
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  intro hEq
  unfold zA zB at hEq
  have : (Complex.I * (Real.sqrt 3 : ℝ)) = 0 := by linear_combination hEq
  rcases mul_eq_zero.1 this with h | h
  · exact Complex.I_ne_zero h
  · exact hs (by exact_mod_cast h)

private lemma primitiveRoots_six : primitiveRoots 6 ℂ = {zA, zB} := by
  ext z
  rw [mem_primitiveRoots (by norm_num), isPrimitiveRoot_six_iff]
  have hfac : z ^ 2 - z + 1 = (z - zA) * (z - zB) := by
    unfold zA zB
    linear_combination (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq
      + (-1 / 4 : ℂ) * sq_sqrt_three
  rw [hfac, mul_eq_zero, sub_eq_zero, sub_eq_zero, Finset.mem_insert, Finset.mem_singleton]

/-- The sum of the primitive 6-th roots of unity equals `μ 6`. -/
theorem mobius_root_sum_6 :
    ∑ ζ ∈ primitiveRoots 6 ℂ, ζ = (ArithmeticFunction.moebius 6 : ℂ) := by
  have hmu : ArithmeticFunction.moebius 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (show Nat.Coprime 2 3 by decide),
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  rw [primitiveRoots_six, Finset.sum_pair zA_ne_zB, hmu]
  unfold zA zB
  push_cast
  ring

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

