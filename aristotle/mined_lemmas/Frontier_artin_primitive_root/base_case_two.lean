import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a primitive root modulo the prime `p` if its residue generates the
multiplicative group `(ZMod p)ˣ`, i.e. it has multiplicative order `p - 1`. -/

theorem base_case_two : ({5, 11, 13} : Set ℕ) ⊆ artinPrimes 2 := by
  rintro p (rfl | rfl | rfl)
  · exact ⟨by norm_num, isPrimitiveRootMod_two_five⟩
  · exact ⟨by norm_num, isPrimitiveRootMod_two_eleven⟩
  · exact ⟨by norm_num, isPrimitiveRootMod_two_thirteen⟩

end Frontier

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

