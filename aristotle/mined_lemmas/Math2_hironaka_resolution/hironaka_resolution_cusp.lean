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
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable (k : Type*) [Field k]

/-- The affine plane curve `C_{a,b} : y^a = x^b` over a field `k`.
For `a, b ≥ 2` coprime this is the standard quasi-homogeneous plane curve singularity
(for `(a,b) = (2,3)` it is the cuspidal cubic `y² = x³`). -/

theorem hironaka_resolution_cusp {k : Type*} [Field k] [CharZero k] :
    (∀ t : k, cuspParam k 2 3 t ∈ cuspCurve k 2 3) ∧
    Function.Injective (cuspParam k 2 3) ∧
    Set.range (cuspParam k 2 3) = cuspCurve k 2 3 := by
  obtain ⟨-, -, h1, h2, h3, -⟩ :=
    hironaka_resolution (k := k) (a := 2) (b := 3) le_rfl (by norm_num) (by decide)
  exact ⟨h1, h2, h3⟩

end Math2

