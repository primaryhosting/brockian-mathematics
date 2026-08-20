import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma prod_oddPrimesLe_one_add_four_div_le {q : ℕ} (hq : 1 ≤ q) :
    ∏ p ∈ oddPrimesLe (2 ^ q), (1 + 4 / (p : ℝ)) ≤ Real.exp 20 * (q : ℝ) ^ 16 := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : ∏ p ∈ oddPrimesLe (2 ^ q), (1 + 4 / (p : ℝ))
      ≤ ∏ p ∈ oddPrimesLe (2 ^ q), Real.exp (4 / (p : ℝ)) := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast oddPrimesLe_three_le hp
      positivity
    · have := Real.add_one_le_exp (4 / (p : ℝ))
      linarith
  rw [← Real.exp_sum] at h1
  have h2 : ∑ p ∈ oddPrimesLe (2 ^ q), (4 / (p : ℝ))
      ≤ 4 * ∑ p ∈ Nat.primesBelow (2 ^ q + 1), (1 / (p : ℝ)) := by
    rw [Finset.mul_sum]
    have hsub : ∑ p ∈ oddPrimesLe (2 ^ q), (4 * (1 / (p : ℝ)))
        ≤ ∑ p ∈ Nat.primesBelow (2 ^ q + 1), (4 * (1 / (p : ℝ))) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (oddPrimesLe_subset_primesBelow _) ?_
      intro p hp _
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hp2
      positivity
    calc ∑ p ∈ oddPrimesLe (2 ^ q), (4 / (p : ℝ))
        = ∑ p ∈ oddPrimesLe (2 ^ q), (4 * (1 / (p : ℝ))) := by
          refine Finset.sum_congr rfl (fun p _ => by ring)
      _ ≤ _ := hsub
  have h3 := sum_inv_primesBelow_pow_two_le hq
  have h4 : ∑ p ∈ oddPrimesLe (2 ^ q), (4 / (p : ℝ)) ≤ 20 + 16 * Real.log q := by
    linarith
  have h5 : Real.exp (∑ p ∈ oddPrimesLe (2 ^ q), (4 / (p : ℝ))) ≤ Real.exp (20 + 16 * Real.log q) :=
    Real.exp_le_exp.mpr h4
  have h6 : Real.exp (20 + 16 * Real.log q) = Real.exp 20 * (q : ℝ) ^ 16 := by
    rw [Real.exp_add]
    congr 1
    rw [show (16 : ℝ) * Real.log q = Real.log ((q : ℝ) ^ 16) by
      rw [Real.log_pow]; push_cast; ring]
    exact Real.exp_log (by positivity)
  linarith [h1, h5, h6.le, h6.ge]

end Brun

import Mathlib

/-!
# Definitions for Brun's theorem

Basic counting functions used in the proof that the sum of reciprocals of twin primes
converges.
-/

namespace Brun

open Finset

/-- The odd primes `≤ z`. -/
