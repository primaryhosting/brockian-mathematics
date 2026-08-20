/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, in the standard trial-division form:
`p` is at least `2` and has no divisor `m` with `2 ≤ m < p`.

This file is deliberately kept free of imports so that the required module
header can be the very first item in the file (Lean forbids `import` after a
module docstring).  The companion file
`RequestProject/GoldbachWheelK2_631_Mathlib.lean` proves
`IsPrimeNat p ↔ Nat.Prime p`, so the statement below is exactly the usual
Goldbach statement phrased with Mathlib's `Nat.Prime`. -/

theorem goldbachWheelK2_631_mathlib (n : ℕ) (h4 : 4 ≤ n) (h631 : n ≤ 631) (hev : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_631 n h4 h631 hev.two_dvd
  exact ⟨p, q, (isPrimeNat_iff_prime p).mp hp, (isPrimeNat_iff_prime q).mp hq, hpq⟩

end Brockian

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

