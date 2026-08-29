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
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.GoldbachSchema

noncomputable section

/-- The additive character `e(x) = exp(2πi x)` on the circle. -/

lemma primeExpSum_sq (n : ℕ) (t : ℝ) :
    (primeExpSum n t) ^ 2 =
      ∑ pq ∈ ((Finset.range (n + 1)).filter Nat.Prime) ×ˢ
              ((Finset.range (n + 1)).filter Nat.Prime),
        e (((pq.1 + pq.2 : ℕ) : ℝ) * t) := by
  rw [sq, primeExpSum, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [← e_add]
  congr 1
  push_cast
  ring

/-- **Exactness of the spectral model**: the spectral count of `n` is precisely the
number of ordered pairs of primes summing to `n`. -/
