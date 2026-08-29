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

lemma sigma1_mul_prime_pow {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (j : ℕ) :
    sigma1 (n * p ^ j) = sigma1 n * ∑ i ∈ Finset.range (j + 1), p ^ i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sigma1_mul_prime_pow_succ hp hpn, ih,
      Finset.sum_range_succ (f := fun i => p ^ i) (n := j + 1)]
    ring

