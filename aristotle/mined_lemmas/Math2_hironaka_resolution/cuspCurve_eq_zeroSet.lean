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

lemma cuspCurve_eq_zeroSet (a b : ℕ) :
    cuspCurve k a b = {p : k × k | MvPolynomial.eval ![p.1, p.2] (cuspPoly k a b) = 0} := by
  ext p
  simp only [cuspCurve, cuspPoly, Set.mem_setOf_eq, map_sub, map_pow, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_zero]

/-- The origin lies on the curve and both partial derivatives of the defining equation
vanish there: the origin is a singular point (Jacobian criterion). -/
