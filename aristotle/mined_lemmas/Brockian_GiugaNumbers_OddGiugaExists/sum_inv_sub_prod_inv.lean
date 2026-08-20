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

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite number `n > 1` such that `p ∣ n / p - 1` for every
prime `p` dividing `n`. -/

lemma sum_inv_sub_prod_inv (h0 : ∀ q ∈ S, q ≠ 0) :
    (∑ p ∈ S, (p : ℚ)⁻¹) - (∏ p ∈ S, (p : ℚ)⁻¹)
      = (((∑ q ∈ S, ∏ r ∈ S.erase q, (r : ℤ)) - 1 : ℤ) : ℚ) / ((∏ p ∈ S, p : ℕ) : ℚ) := by
  classical
  have hne : ∀ q ∈ S, (q : ℚ) ≠ 0 := fun q hq => Nat.cast_ne_zero.mpr (h0 q hq)
  have hN : ((∏ p ∈ S, p : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr hne
  rw [eq_div_iff hN, sub_mul, Finset.sum_mul]
  have h1 : ∀ p ∈ S, (p : ℚ)⁻¹ * ((∏ q ∈ S, q : ℕ) : ℚ) = ∏ r ∈ S.erase p, (r : ℚ) := by
    intro p hp
    rw [Nat.cast_prod, ← Finset.mul_prod_erase S (fun q => ((q : ℚ))) hp, ← mul_assoc,
      inv_mul_cancel₀ (hne p hp), one_mul]
  have h2 : (∏ p ∈ S, (p : ℚ)⁻¹) * ((∏ q ∈ S, q : ℕ) : ℚ) = 1 := by
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun p hp => inv_mul_cancel₀ (hne p hp)
  rw [Finset.sum_congr rfl h1, h2]
  push_cast
  ring

/-- The rational criterion is equivalent to the divisibility criterion. -/
