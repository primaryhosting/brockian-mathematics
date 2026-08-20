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

A *Zumkeller number* is a positive integer whose divisors can be split into two sets with
equal sums.  Here we prove that an odd Zumkeller number must have at least three distinct
prime factors.

The argument: a Zumkeller number is perfect or abundant (`σ(n) ≥ 2n`), while an odd number
with at most two distinct prime factors `p < q` satisfies
`σ(n)/n < p/(p-1) · q/(q-1) ≤ (3/2)(5/4) < 2`, hence is deficient.
-/

open scoped BigOperators

set_option maxRecDepth 40000

namespace Brockian.ZumkellerNumbers

/-- `n` is a *Zumkeller number* if it is positive and its set of divisors can be split into
two parts having the same sum. -/

theorem OddZumkellerFrom3Structure {n : ℕ} (hodd : Odd n) (hz : IsZumkeller n) :
    3 ≤ n.primeFactors.card := by
  by_contra hcon
  have hcard : n.primeFactors.card ≤ 2 := by omega
  have h1 := two_mul_le_sigma_of_isZumkeller hz
  have h2 := sigma_lt_two_mul_of_card_le_two hz.1 hodd hcard
  omega

/-- `945` is an odd Zumkeller number, witnessing that the hypotheses of
`OddZumkellerFrom3Structure` are satisfiable. -/
