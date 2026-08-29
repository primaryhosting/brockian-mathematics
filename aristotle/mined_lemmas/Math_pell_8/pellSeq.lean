import Mathlib

/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
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

namespace Math

/-- **Pell's equation for `d = 8`.** The equation `x² − 8·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (equivalently `x ≠ ±1`): take `(x, y) = (3, 1)`. -/

def pellSeq : ℕ → ℤ × ℤ
  | 0 => (3, 1)
  | n + 1 => (3 * (pellSeq n).1 + 8 * (pellSeq n).2, (pellSeq n).1 + 3 * (pellSeq n).2)

/-- Every term of `pellSeq` solves `x² − 8·y² = 1`. -/
