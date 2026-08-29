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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

/-- `sigmaOne n` is the sum of the divisors of `n`. -/

lemma kHyperperfect_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : q + p = p * p + 1) : KHyperperfect (p - 1) (p * q) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hlt : p < q := by nlinarith
  have hne : p ≠ q := Nat.ne_of_lt hlt
  have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have h1 : (1 : ℕ) ≤ p := le_trans (by norm_num) hp2
    push_cast [h1]
    ring
  have hq' : (q : ℤ) + (p : ℤ) = (p : ℤ) * (p : ℤ) + 1 := by exact_mod_cast hpq
  refine ⟨by omega, ?_⟩
  rw [sigmaOne_mul_primes hp hq hne, hcast]
  push_cast
  nlinarith [hq']

