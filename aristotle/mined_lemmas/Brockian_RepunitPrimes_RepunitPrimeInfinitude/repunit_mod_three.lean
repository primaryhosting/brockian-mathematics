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

/-- The `n`-th repunit `R n = 1 + 10 + ... + 10^(n-1) = (10^n - 1)/9`, i.e. the number
whose decimal expansion consists of `n` ones. -/

lemma repunit_mod_three (n : ℕ) : ((repunit n : ℕ) : ZMod 3) = (n : ZMod 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h10 : ((10 : ZMod 3)) = 1 := by decide
      push_cast [repunit_succ] at ih ⊢
      rw [ih, h10]
      ring

