/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede every doc comment, so the header above is
-- written as a plain block comment and repeated verbatim as the module doc comment below.)

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
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

namespace Math2

open MvPolynomial

/-! ## Setup

We work with the affine plane curves `y ^ a = x ^ b` over a field `k` of characteristic
zero, given by the polynomial `curve k a b = Y ^ a - X ^ b` in `MvPolynomial (Fin 2) k`
(`X = X 0`, `Y = X 1`).  These are exactly the singularities resolved by the classical
Euclidean/continued-fraction sequence of point blowups.

Blowing up the origin of the affine plane is covered by two charts:

* the `x`-chart, `(x, y) ↦ (x, x * y)`;
* the `y`-chart, `(x, y) ↦ (x * y, y)`.

The *total transform* of a curve `p` is its pullback along one of these substitutions; the
*strict transform* is obtained by removing the largest possible power of the exceptional
divisor (`x`, resp. `y`) from the total transform.  This is the content of `BlowupStep`.
-/

/-- The plane curve `y ^ a = x ^ b`, as the polynomial `Y ^ a - X ^ b`. -/

theorem cusp_resolution :
    BlowupStep (curve ℚ 2 3) (curve ℚ 2 1) ∧ SmoothAtOrigin (curve ℚ 2 1) :=
  ⟨by simpa using blowupStep_x (k := ℚ) (a := 2) (b := 3) (by norm_num) (by norm_num),
    smoothAtOrigin_curve_one_right 2⟩

end Math2

#print axioms Math2.hironaka_resolution
#print axioms Math2.hironaka_resolution_of_ne_zero
#print axioms Math2.cusp_resolution

