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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RepunitPrimes

open Finset

/-- The `n`-th base-`b` repunit: `1 + b + b^2 + ⋯ + b^(n-1)`. -/

lemma repunitBase_mul (b a k : ℕ) :
    repunitBase b (a * k) = repunitBase b a * repunitBase (b ^ a) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : a * (k + 1) = a * k + a := by ring
      have e1 : repunitBase b (a * k + a)
          = repunitBase b (a * k) + ∑ i ∈ range a, b ^ (a * k + i) := by
        simp only [repunitBase]; exact Finset.sum_range_add _ _ _
      rw [h, e1, ih, repunitBase_succ (b ^ a) k, Nat.mul_add]
      congr 1
      simp only [repunitBase, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_add, pow_mul, mul_comm]

/-- If `a ∣ n` then `R a ∣ R n`. -/
