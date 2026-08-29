/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
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

set_option grind.warning false

namespace Math2

/-- The degree of a divisor `D` on a curve whose (closed) points are indexed by `P`,
where `degPt p` is the degree of the point `p` (equal to `1` when the base field is
algebraically closed).  A divisor is a finitely supported formal `ℤ`-combination of points. -/

noncomputable def eulerChar (h0 h1 : (P →₀ ℤ) → ℕ) (D : P →₀ ℤ) : ℤ :=
  (h0 D : ℤ) - (h1 D : ℤ)

/-- Adding one point to a divisor increases the Euler characteristic by the degree of that
point; this is the additivity hypothesis, coming from the skyscraper exact sequence
`0 → O(D) → O(D + p) → k(p) → 0`.  Here it is restated for subtraction of a point. -/
