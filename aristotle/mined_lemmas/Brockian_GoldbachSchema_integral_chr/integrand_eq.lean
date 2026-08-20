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
# A spectral (circle-method) schema for the Goldbach conjecture

This file sets up the "spectral model" for the binary Goldbach problem: the number of
representations of `n` as an ordered sum of two primes is computed by an exponential-sum
(Fourier) integral over the unit circle, and Goldbach's conjecture is exactly the
statement that this integral is positive for every even `n ≥ 4`.

Main results:

* `Brockian.GoldbachSchema.spectral_identity` : the Fourier integral of the squared prime
  exponential sum equals the representation count. This is the unconditional analytic input.
* `Brockian.GoldbachSchema.goldbach_from_spectral_model` : from the spectral positivity
  hypothesis one deduces Goldbach's conjecture.
* `Brockian.GoldbachSchema.spectralPositivity_iff_goldbach` : the spectral positivity
  hypothesis is *equivalent* to Goldbach's conjecture, so it cannot be discharged without
  proving Goldbach itself.
* `Brockian.GoldbachSchema.goldbach_below_two_hundred` : an unconditional finite verification.
-/

namespace Brockian.GoldbachSchema

open Complex Real Finset

/-- The primes not exceeding `n`. -/

theorem integrand_eq (n : ℕ) (a : ℝ) :
    (primeExpSum n a) ^ 2 * chr (-(n : ℤ)) a =
      ∑ x ∈ primesUpTo n ×ˢ primesUpTo n, chr ((x.1 : ℤ) + (x.2 : ℤ) - (n : ℤ)) a := by
  rw [Finset.sum_product' (s := primesUpTo n) (t := primesUpTo n)
    (f := fun i j => chr ((i : ℤ) + (j : ℤ) - (n : ℤ)) a)]
  unfold primeExpSum
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [chr_mul, chr_mul]
  ring_nf

