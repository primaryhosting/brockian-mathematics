/-
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-- The set of primitive `2`-nd roots of unity in `ℂ` is `{-1}`. -/
theorem primitiveRoots_two_complex : primitiveRoots 2 ℂ = {(-1 : ℂ)} := by
  ext x
  rw [mem_primitiveRoots (by norm_num), Finset.mem_singleton]
  constructor
  · intro hx
    have h2 : x ^ 2 = 1 := hx.pow_eq_one
    have h1 : x ≠ 1 := by
      intro h
      have := hx.dvd_of_pow_eq_one 1 (by simp [h])
      omega
    have h0 : (x - 1) * (x + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h) h1
    · linear_combination h
  · rintro rfl
    refine ⟨by norm_num, fun l hl => ?_⟩
    rcases Nat.even_or_odd l with he | ho
    · exact he.two_dvd
    · rw [ho.neg_one_pow] at hl
      norm_num at hl

/-- The sum of the primitive `2`-nd roots of unity equals `μ(2) = -1`. -/
theorem mobius_root_sum_2 :
    ∑ x ∈ primitiveRoots 2 ℂ, x = (ArithmeticFunction.moebius 2 : ℂ) := by
  rw [primitiveRoots_two_complex]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

end Math

