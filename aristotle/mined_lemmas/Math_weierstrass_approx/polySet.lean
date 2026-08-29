/-
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Weierstrass Approx
Category: Pure Mathematics
Target: Math.weierstrass_approx
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

open scoped Polynomial

/-- The set of elements of `C([a,b], ℝ)` which are restrictions of real polynomials. -/

def polySet (a b : ℝ) : Set C(Set.Icc a b, ℝ) :=
  Set.range fun p : ℝ[X] => p.toContinuousMapOn (Set.Icc a b)

/-- **Weierstrass approximation theorem**: the polynomial functions are dense in
`C([a,b], ℝ)` equipped with the sup norm. -/
