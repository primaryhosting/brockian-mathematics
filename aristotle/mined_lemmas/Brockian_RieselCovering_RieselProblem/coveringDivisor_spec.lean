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

theorem coveringDivisor_spec (n : Nat) :
    1 < coveringDivisor n ∧ coveringDivisor n ≤ 241 ∧ coveringDivisor n ∣ k * 2 ^ n - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := coveringTable_spec (n % 24) (Nat.mod_lt n (by decide))
  refine ⟨h1, h2, ?_⟩
  have hn : n % 24 + 24 * (n / 24) = n := Nat.mod_add_div n 24
  have := dvd_shift_iter (p := coveringDivisor n) h3 h4 (n / 24)
  rwa [hn] at this

/-- **The Riesel problem (Riesel's witness `k = 509203`).**
For every `n ≥ 1` the number `509203 * 2 ^ n - 1` is composite: it admits a divisor `d`
with `1 < d < 509203 * 2 ^ n - 1`.  Hence `509203` is a Riesel number. -/
