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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RieselCovering

/-- A *Riesel number* is a positive odd natural number `k` such that `k * 2 ^ n - 1`
is composite (never prime) for every `n ≥ 1`. -/

theorem two_pow_modEq (n : ℕ) : (2 : ℕ) ^ n ≡ 2 ^ (n % 24) [MOD 16777215] := by
  conv_lhs => rw [← Nat.div_add_mod n 24, pow_add, pow_mul]
  have h : ((2 : ℕ) ^ 24) ^ (n / 24) ≡ 1 ^ (n / 24) [MOD 16777215] :=
    Nat.ModEq.pow _ (by decide)
  simpa using h.mul_right ((2 : ℕ) ^ (n % 24))

/-- The core covering step: if a prime `p` divides `2 ^ 24 - 1` and divides
`509203 * 2 ^ r - 1` where `r = n % 24`, then `p` divides `509203 * 2 ^ n - 1`. -/
