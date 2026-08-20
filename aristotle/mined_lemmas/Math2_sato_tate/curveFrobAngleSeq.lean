/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Set Filter Topology WeierstrassCurve

namespace Math2

/-! ## The Sato–Tate distribution

The Sato–Tate distribution is the probability measure on the interval `[0, π]` of Frobenius
angles with density `(2/π) · sin²θ` with respect to Lebesgue measure.  For an elliptic curve
`E / ℚ` without complex multiplication, with trace of Frobenius `a_p` at a prime `p` of good
reduction, the Hasse bound `|a_p| ≤ 2√p` lets one write `a_p = 2√p · cos θ_p` with
`θ_p ∈ [0, π]`, and the Sato–Tate theorem asserts that the angles `θ_p` are equidistributed
in `[0, π]` with respect to this measure.
-/

/-- The density of the Sato–Tate distribution: `θ ↦ (2/π) sin²θ`. -/

noncomputable def curveFrobAngleSeq (W : WeierstrassCurve ℤ) (n : ℕ) : ℝ :=
  frobAngleSeq (curveTraceOfFrobenius W) n

/-- The thirteen `j`-invariants of elliptic curves over `ℚ` with complex multiplication. -/
