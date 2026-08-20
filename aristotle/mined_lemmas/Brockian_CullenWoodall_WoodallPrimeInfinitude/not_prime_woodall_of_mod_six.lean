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

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; note `W 0 = 0`). -/

theorem not_prime_woodall_of_mod_six {n : ℕ} (h : n % 6 = 4 ∨ n % 6 = 5) :
    ¬ (woodall n).Prime := by
  intro hp
  have hdvd := three_dvd_woodall h
  have h3 : (3 : ℕ) = woodall n :=
    (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd).resolve_left (by norm_num)
  have h4 : 4 ≤ n := by omega
  have hle : woodall 4 ≤ woodall n := woodall_monotone h4
  have h63 : woodall 4 = 63 := rfl
  omega

/-- There are infinitely many composite Woodall numbers. -/
