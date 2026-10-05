import Mathlib

/-!
# Nat Cast Add
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.natCast_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace RequestProject

/-- The canonical map `ℕ → Ordinal` sends `0` to `0`. -/

theorem natCast_succ_ordinal (n : ℕ) : ((n + 1 : ℕ) : Ordinal) = (n : Ordinal) + 1 :=
  Nat.cast_succ n

/-- Finite-ordinal addition agrees with natural number addition:
`((m + n : ℕ) : Ordinal) = (m : Ordinal) + (n : Ordinal)`.

Proved by induction on `n`, using associativity of ordinal addition. -/
