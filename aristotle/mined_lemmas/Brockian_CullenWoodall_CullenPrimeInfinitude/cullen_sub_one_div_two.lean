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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The infinitude of Cullen primes (primes of the form `n * 2 ^ n + 1`) is an open
problem.  This file gives a Lean-checked *conditional reduction*: the infinitude of
Cullen primes follows from the existence of arbitrarily large odd `n` admitting a
Proth witness, i.e. an `a` with `a ^ ((n * 2 ^ n) / 2) = -1` modulo `n * 2 ^ n + 1`.
This is exactly the criterion (Proth's theorem, proved here from scratch) that is
used in practice to certify Cullen primes, and for odd `n` the condition is in fact
*equivalent* to primality of the Cullen number.

The file also contains unconditional results in the opposite direction: every odd
prime `p` divides the Cullen number `cullen (p - 2)`, hence infinitely many Cullen
numbers are composite.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem cullen_sub_one_div_two {n : ℕ} (hn : 0 < n) :
    (cullen n - 1) / 2 = n * 2 ^ (n - 1) := by
  have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have : cullen n - 1 = n * 2 ^ (n - 1) * 2 := by
    simp [cullen, h2, mul_assoc]
  rw [this, Nat.mul_div_cancel _ (by norm_num)]

/-- A Proth witness certifies that the Cullen number `cullen n` is prime (`n` odd). -/
