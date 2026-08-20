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

lemma criterion_iff (hS : ∀ p ∈ S, p.Prime) :
    (∃ k : ℤ, (∑ p ∈ S, (p : ℚ)⁻¹) - (∏ p ∈ S, (p : ℚ)⁻¹) = (k : ℚ)) ↔
      ∀ p ∈ S, (p : ℤ) ∣ ((∏ r ∈ S.erase p, (r : ℤ)) - 1) := by
  have h0 : ∀ q ∈ S, q ≠ 0 := fun q hq => (hS q hq).ne_zero
  have hN' : (∏ x ∈ S, (x : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq => Nat.cast_ne_zero.mpr (h0 q hq)
  have hN : ((∏ p ∈ S, p : ℕ) : ℚ) ≠ 0 := by rw [Nat.cast_prod]; exact hN'
  rw [← prod_dvd_numerator_iff hS, sum_inv_sub_prod_inv h0]
  constructor
  · rintro ⟨k, hk⟩
    rw [div_eq_iff hN] at hk
    refine ⟨k, ?_⟩
    have : ((((∑ q ∈ S, ∏ r ∈ S.erase q, (r : ℤ)) - 1 : ℤ)) : ℚ)
        = (((∏ p ∈ S, p : ℕ) : ℤ) * k : ℤ) := by push_cast; push_cast at hk; linarith
    exact_mod_cast this
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    exact mul_div_cancel_left₀ _ hN'

end Helpers

/-- Every Giuga number is squarefree. -/
