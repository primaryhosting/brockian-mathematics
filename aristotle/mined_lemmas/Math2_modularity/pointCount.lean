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

noncomputable def pointCount (E : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card (E.map (Int.castRingHom (ZMod p))).toAffine.Point

/-- The trace of Frobenius `a_p(E) = p + 1 - #E(𝔽_p)` of an integral Weierstrass curve. -/
