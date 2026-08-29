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

def IsModular (E : WeierstrassCurve ℚ) : Prop :=
  ∃ (E₀ : WeierstrassCurve ℤ) (C : WeierstrassCurve.VariableChange ℚ),
    C • (E₀.map (Int.castRingHom ℚ)) = E ∧ IsModularIntegral E₀

/-- The full Shimura–Taniyama–Weil statement: every elliptic curve over `ℚ` is modular. -/
