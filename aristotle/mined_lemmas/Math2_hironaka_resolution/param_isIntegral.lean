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

lemma param_isIntegral (hp : p ≠ 0) :
    IsIntegral
      (Algebra.adjoin k ({Polynomial.X ^ p, Polynomial.X ^ q} : Set (Polynomial k)))
      (Polynomial.X : Polynomial k) := by
  set A := Algebra.adjoin k ({Polynomial.X ^ p, Polynomial.X ^ q} : Set (Polynomial k))
  have hmem : (Polynomial.X ^ p : Polynomial k) ∈ A := Algebra.subset_adjoin (by simp)
  exact ⟨Polynomial.X ^ p - Polynomial.C (⟨Polynomial.X ^ p, hmem⟩ : A),
    Polynomial.monic_X_pow_sub_C _ hp, by simp⟩

/-- The parametrization is injective. -/
