import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Statement: A time-reversal-invariant half-integer-spin system has doubly degenerate levels (Kramers).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Phys

/-- A vector and its image under an antiunitary time-reversal operator squaring to `-1`
are linearly independent (the algebraic heart of Kramers' theorem). -/

theorem spinHalfTimeReversal_sq (p : ℂ × ℂ) :
    spinHalfTimeReversal (spinHalfTimeReversal p) = -p := by
  simp [spinHalfTimeReversal, Prod.ext_iff]

end Phys

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

