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

lemma param_injective (hp : p ≠ 0) (hcop : Nat.Coprime p q) :
    Function.Injective (param (k := k) p q) := by
  obtain ⟨a, b, hab⟩ := exists_bezout hcop
  intro s t hst
  have h0 : s ^ p = t ^ p := congrFun hst 0
  have h1 : s ^ q = t ^ q := congrFun hst 1
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    have : t ^ p = 0 := by simpa [zero_pow hp] using h0.symm
    exact (pow_eq_zero_iff hp).mp this |>.symm
  · have ht : t ≠ 0 := by
      intro h
      subst h
      exact hs ((pow_eq_zero_iff hp).mp (by simpa [zero_pow hp] using h0))
    rw [← zpow_bezout hab hs, ← zpow_bezout hab ht, h0, h1]

/-- Every point of the curve is in the image of the parametrization; the preimage is given by
an explicit monomial with integer exponents. -/
