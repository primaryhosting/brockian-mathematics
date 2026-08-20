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
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

theorem sum_inv_primesBelow_le (z : ℕ) :
    ∑ p ∈ (z + 1).primesBelow, (1 : ℝ) / p
      ≤ 4 * (1 + Real.log (Nat.log 2 z)) := by
  set J := Nat.log 2 z with hJ
  have hmaps : ∀ p ∈ (z + 1).primesBelow, Nat.log 2 p ∈ Finset.Icc 1 J := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hplt : p < z + 1 := Nat.lt_of_mem_primesBelow hp
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · have : 1 ≤ Nat.log 2 p := by
        rw [Nat.one_le_iff_ne_zero, Ne, Nat.log_eq_zero_iff]
        push_neg
        exact ⟨hpp.two_le, by norm_num⟩
      exact this
    · exact Nat.log_mono_right (by omega)
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun p => (1 : ℝ) / p)
  rw [← hfib]
  have hbound : ∑ j ∈ Finset.Icc 1 J, ∑ p ∈ (z + 1).primesBelow with Nat.log 2 p = j, (1:ℝ) / p
      ≤ ∑ j ∈ Finset.Icc 1 J, (4 : ℝ) / j := by
    refine Finset.sum_le_sum fun j hj => ?_
    exact sum_inv_dyadic_block_le z j (Finset.mem_Icc.mp hj).1
  refine hbound.trans ?_
  have hharm : ∑ j ∈ Finset.Icc 1 J, (4 : ℝ) / j = 4 * ((harmonic J : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv]
  rw [hharm]
  have := harmonic_le_one_add_log J
  linarith

/-- A Mertens-type upper bound: `∏_{p ≤ z} (1 + 4/p)` grows at most like a power of `log z`. -/
