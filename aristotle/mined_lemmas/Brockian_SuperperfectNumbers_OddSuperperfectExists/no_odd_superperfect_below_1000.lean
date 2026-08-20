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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

lemma no_odd_superperfect_below_1000 {n : ℕ} (hlt : n < 1000) (hn : Odd n) :
    ¬ Superperfect n := by
  have key : ∀ m < 1000, m % 2 = 1 →
      (∑ d ∈ (∑ e ∈ (m : ℕ).divisors, e).divisors, d) ≠ 2 * m := by
    decide +kernel
  have hn' : n % 2 = 1 := Nat.odd_iff.mp hn
  intro hs
  rw [Superperfect, sig_eq_sum, sig_eq_sum] at hs
  exact key n hlt hn' hs

/-- **Odd superperfect numbers: a conditional reduction.**

Whether an odd superperfect number exists is an open problem; no unconditional
existence proof is given here.  What is proved is a reduction: an odd superperfect
number exists if and only if one exists that is larger than `1000`, is not prime,
and whose sum-of-divisors `σ(n) = 2 ^ a * k` (with `k` odd) satisfies
`(2 ^ (a+1) - 1) * σ(k) = 2 * n`. -/
