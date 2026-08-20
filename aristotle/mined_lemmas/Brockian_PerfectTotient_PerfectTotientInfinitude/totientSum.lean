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
# Perfect Totient Infinitude
Category: Brockian Conjecture
Target: Brockian.PerfectTotient.PerfectTotientInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.PerfectTotient

open Nat

/-- `totientSum n` is the sum of the iterated totients
`φ(n) + φ(φ(n)) + ⋯ + 1` of `n`, the iteration stopping once the value `1` is
reached (and `1` being the final summand).  By convention it is `0` for `n ≤ 1`. -/

def totientSum : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (n + 2) => Nat.totient (n + 2) + totientSum (Nat.totient (n + 2))
  decreasing_by exact Nat.totient_lt _ (by omega)

/-- A natural number `n` is a *perfect totient number* when it is positive and equals
the sum of its iterated totients `φ(n) + φ(φ(n)) + ⋯ + 1`. -/
