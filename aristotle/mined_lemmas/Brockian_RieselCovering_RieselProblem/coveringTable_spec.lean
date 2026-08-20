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

theorem coveringTable_spec :
    ∀ r, r < 24 →
      1 < coveringTable.getD r 3 ∧ coveringTable.getD r 3 ≤ 241 ∧
        coveringTable.getD r 3 ∣ 16777215 ∧
        coveringTable.getD r 3 ∣ k * 2 ^ r - 1 := by
  decide

/-- Periodicity step: since `p ∣ 2 ^ 24 - 1`, divisibility of `k * 2 ^ n - 1` by `p`
propagates from `n` to `n + 24`. -/
