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

lemma sum_divisors_three_pow_mul_35 (b : ℕ) :
    (∑ d ∈ (3 ^ b * 35 : ℕ).divisors, (d : ℤ)) = 24 * (3 ^ (b + 1) - 1) := by
  have hcop : Nat.Coprime (3 ^ b) 35 := Nat.Coprime.pow_left _ (by decide)
  have h1 : ∑ d ∈ (3 ^ b * 35 : ℕ).divisors, d
      = (∑ d ∈ (3 ^ b : ℕ).divisors, d) * ∑ d ∈ (35 : ℕ).divisors, d :=
    Nat.Coprime.sum_divisors_mul hcop
  have h2 : ∑ d ∈ (35 : ℕ).divisors, d = 48 := by decide
  have h3 : ∑ d ∈ (3 ^ b : ℕ).divisors, d = ∑ i ∈ Finset.range (b + 1), 3 ^ i :=
    Nat.sum_divisors_prime_pow (by norm_num)
  have h4 : (∑ d ∈ (3 ^ b * 35 : ℕ).divisors, (d : ℤ))
      = ((∑ d ∈ (3 ^ b * 35 : ℕ).divisors, d : ℕ) : ℤ) := by push_cast; ring
  rw [h4, h1, h2, h3]
  push_cast
  have h5 := two_mul_geom_sum (b + 1)
  linarith

/-- The inductive step gadget: from a set `T` of divisors of `35` and a set `A` of divisors of
`3 ^ b * 35` we build a set of divisors of `3 ^ (b + 1) * 35` whose sum is
`(∑ T) + 3 * (∑ A)`. -/
