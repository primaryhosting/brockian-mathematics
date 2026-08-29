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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset Pointwise

/-! ## Basic definitions -/

/-- The sum of the (positive) divisors of `n`. -/

lemma disjoint_divisors_mul_prime_pow {n p j : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    Disjoint (n.divisors * ({p ^ (j + 1)} : Finset ℕ)) (n * p ^ j).divisors := by
  rw [Finset.disjoint_left]
  rintro x hx hx2
  rw [Finset.mem_mul] at hx
  obtain ⟨d, hd, c, hc, rfl⟩ := hx
  simp only [Finset.mem_singleton] at hc
  subst hc
  rw [Nat.mem_divisors] at hd hx2
  have h1 : p ^ (j + 1) ∣ n * p ^ j := dvd_trans ⟨d, by ring⟩ hx2.1
  rw [pow_succ, mul_comm n (p ^ j)] at h1
  exact hpn ((mul_dvd_mul_iff_left (a := p ^ j) (pow_ne_zero _ hp.pos.ne')).mp h1)

