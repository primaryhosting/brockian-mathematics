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
# Riesel Problem — Mathlib interface

Companion to `Brockian.RieselCovering` (which is import-free): the same result phrased with
Mathlib's `Nat.Prime`.
-/

namespace Brockian
namespace RieselCovering

/-- `509203 * 2 ^ n - 1` is not prime for any `n ≥ 1`, stated with `Nat.Prime`. -/

theorem dvd_shift_iter {p r : Nat} (h24 : p ∣ 16777215) (h0 : p ∣ k * 2 ^ r - 1) :
    ∀ q, p ∣ k * 2 ^ (r + 24 * q) - 1 := by
  intro q
  induction q with
  | zero => simpa using h0
  | succ q ih =>
      have e : r + 24 * (q + 1) = (r + 24 * q) + 24 := by omega
      rw [e]
      exact dvd_shift h24 ih

/-- **The covering property**: for every `n`, `coveringDivisor n` is a divisor of
`509203 * 2 ^ n - 1` lying strictly between `1` and `242`. -/
