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

theorem modularity
    (H : ∀ A B : ℤ, 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 → IsModularIntegral ⟨0, 0, 0, A, B⟩) :
    ModularityStatement := by
  intro E hE
  obtain ⟨A, B, C, hAB, hC⟩ := exists_integral_shortModel E hE
  exact ⟨⟨0, 0, 0, A, B⟩, C, hC, H A B hAB⟩

/-- The modularity statement for all elliptic curves over `ℚ` is equivalent to its special
case for the curves `y² = x³ + Ax + B` with integral coefficients. -/
