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
import Brockian.RieselCovering

/-!
# Riesel problem, Mathlib-facing statement

`Brockian.RieselCovering` must begin with a mandated header comment, which forces it to be
import-free (Lean requires `import`s to come first in a file).  This module imports Mathlib and
restates the main result using Mathlib's `Nat.Prime`.
-/

namespace Brockian
namespace RieselCovering


theorem cover_dvd (p r : Nat) (hp24 : p ∣ 16777215) (hr : p ∣ 509203 * 2 ^ r - 1) :
    ∀ q : Nat, p ∣ 509203 * 2 ^ (24 * q + r) - 1 := by
  intro q
  induction q with
  | zero => simpa using hr
  | succ q ih =>
    have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
    have hpow : (2 : Nat) ^ (24 * (q + 1) + r) = 16777216 * 2 ^ (24 * q + r) := by
      rw [← h24, ← Nat.pow_add]; congr 1; omega
    have hone : 1 ≤ (2 : Nat) ^ (24 * q + r) := Nat.one_le_two_pow
    have key : 509203 * 2 ^ (24 * (q + 1) + r) - 1
        = 16777216 * (509203 * 2 ^ (24 * q + r) - 1) + 16777215 := by
      rw [hpow]; omega
    rw [key]
    exact Nat.dvd_add (Nat.dvd_trans ih (Nat.dvd_mul_left _ _)) hp24

/-- **The Riesel problem.**  For every `n ≥ 1` the number `509203 * 2 ^ n - 1` is not prime.

The proof uses the covering set `{3, 5, 7, 13, 17, 241}`; each of these primes divides
`2 ^ 24 - 1 = 16777215`, and for each residue `r < 24` one of them divides
`509203 * 2 ^ r - 1`. -/
