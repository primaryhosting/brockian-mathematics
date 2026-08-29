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

noncomputable def ap (E : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - (pointCount E p : ℤ)

/-- The `n`-th `q`-expansion coefficient of a weight-two cusp form of level `Γ₀(N)`
(the group `Γ₀(N)` has width `1` at the cusp `∞`, so the relevant `q`-parameter
is `q = exp (2πiτ)`). -/
