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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* if its set of divisors can be split into
two parts with equal sums, i.e. there is a set `A` of divisors of `n` whose sum is exactly
half of `σ(n)`. -/

lemma pow_mul_geom (p a : ℕ) :
    p * (∑ i ∈ Finset.range (a + 1), p ^ i) + 1
      = (∑ i ∈ Finset.range (a + 1), p ^ i) + p ^ (a + 1) := by
  induction a with
  | zero => simp; omega
  | succ k ih =>
      rw [Finset.sum_range_succ]
      ring_nf
      ring_nf at ih
      nlinarith [ih, pow_succ p (k + 1)]

/-- For a prime `p ≥ 3`, `σ(p ^ a) < (3 / 2) * p ^ a`. -/
