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

lemma eq_zero_of_coords {x : Fin 2 → k} (h0 : x 0 = 0) (h1 : x 1 = 0) : x = 0 := by
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- A Bézout monomial reconstructs `t` from `t ^ p` and `t ^ q`. -/
