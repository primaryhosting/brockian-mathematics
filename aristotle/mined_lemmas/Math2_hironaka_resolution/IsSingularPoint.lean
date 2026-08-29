/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

open MvPolynomial

variable {k : Type*} [Field k]

/-- The affine plane curve `C_{p,q} : y^p = x^q`, as a polynomial in two variables. -/

def IsSingularPoint (f : MvPolynomial (Fin 2) k) (x : Fin 2 → k) : Prop :=
  eval x f = 0 ∧ ∀ i, eval x (pderiv i f) = 0

/-- The monomial parametrization `𝔸¹ → 𝔸²`, `t ↦ (t^p, t^q)`, of the curve `y^p = x^q`. -/
