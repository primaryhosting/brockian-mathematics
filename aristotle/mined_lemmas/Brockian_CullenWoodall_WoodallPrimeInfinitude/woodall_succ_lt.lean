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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/

lemma woodall_succ_lt (n : ℕ) : woodall n < woodall (n + 1) := by
  have h : n * 2 ^ n + 2 ≤ (n + 1) * 2 ^ (n + 1) := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : (n + 1) * 2 ^ (n + 1) = n * 2 ^ n + (n + 2) * 2 ^ n := by ring
    nlinarith
  simp only [woodall]
  omega

