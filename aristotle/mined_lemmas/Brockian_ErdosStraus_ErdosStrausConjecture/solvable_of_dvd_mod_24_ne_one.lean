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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `Solvable n` means that `4 / n` can be written as a sum of three unit fractions
with positive (natural) denominators. -/

theorem solvable_of_dvd_mod_24_ne_one {d n : ℕ} (hn : 0 < n) (hd : 2 ≤ d) (hdvd : d ∣ n)
    (h : d % 24 ≠ 1) : Solvable n :=
  Solvable.of_dvd hn hdvd (solvable_of_mod_24_ne_one hd h)

/-- A purely arithmetic certificate for solvability: positive `x, y, z` with
`4xyz = n(yz + xz + xy)`. -/
