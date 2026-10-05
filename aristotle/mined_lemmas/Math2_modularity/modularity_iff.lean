/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`, so the required
-- header appears above as a block comment and is repeated as a docstring below.)

import Mathlib

/-!
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open CongruenceSubgroup

namespace Math2

/-- The number of points of the reduction mod `p` of an integral Weierstrass curve,
counted on the affine model together with the point at infinity. -/

theorem modularity_iff :
    ModularityStatement ↔
      ∀ A B : ℤ, 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 →
        IsModular ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℤ).map (Int.castRingHom ℚ)) := by
  constructor
  · intro h A B hAB
    exact h _ (isElliptic_map_shortNF A B hAB)
  · intro h E hE
    obtain ⟨A, B, C, hAB, hC⟩ := exists_integral_shortModel E hE
    rw [← hC]
    exact isModular_variableChange C (h A B hAB)

end Math2

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

