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

namespace Brockian
namespace CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/

lemma mul_two_pow_strictMono : StrictMono (fun n : ℕ => n * 2 ^ n) := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  have h : (n + 1) * 2 ^ (n + 1) = 2 * (n * 2 ^ n) + 2 * 2 ^ n := by ring
  have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
  simp only [h]
  omega

/-- Woodall numbers are strictly increasing from index `1` on. -/
