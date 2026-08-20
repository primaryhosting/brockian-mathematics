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

theorem prod_one_sub_inv_le (z : ℕ) (hz : 3 ≤ z) :
    ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹) ≤ 1 / Real.log z := by
  have hlog : 0 < Real.log z := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < z)
  have hprodpos : 0 < ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_pos fun p hp => one_sub_inv_pos (Nat.prime_of_mem_primesBelow hp)
  have h1 := log_le_prod_inv z (by omega)
  rw [Finset.prod_inv_distrib] at h1
  rw [le_div_iff₀ hlog]
  calc (∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹)) * Real.log z
      ≤ (∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹))
        * (∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹))⁻¹ := by
        exact mul_le_mul_of_nonneg_left h1 hprodpos.le
    _ = 1 := mul_inv_cancel₀ hprodpos.ne'

/-- The main term of Brun's sieve: `∏_{2 < p ≤ z} (1 - 2/p) ≤ 4 / (log z)^2`. -/
