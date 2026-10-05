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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Woodall Prime Infinitude

A *Woodall number* is `W n = n * 2 ^ n - 1`, and a *Woodall prime* is a Woodall
number that is prime.  Whether there are infinitely many Woodall primes is an
open problem, so the target theorem `WoodallPrimeInfinitude` is stated as a
*reduction*: it lists three reformulations of the conjecture and proves them
equivalent (a `TFAE` statement).  Unconditional partial results (explicit
Woodall primes, and basic structural facts) are proved as well.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/

theorem woodall_mono : Monotone woodall := by
  intro m n hmn
  have h : m * 2 ^ m ≤ n * 2 ^ n :=
    Nat.mul_le_mul hmn (Nat.pow_le_pow_right (by norm_num) hmn)
  exact Nat.sub_le_sub_right h 1

/-- On positive indices, Woodall numbers are strictly increasing. -/
