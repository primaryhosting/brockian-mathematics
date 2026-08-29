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
# Introspective numbers

The key algebraic notion in the Agrawal–Kayal–Saxena primality test.
A natural number `m` is *introspective* for a polynomial `f` (with respect to the
modulus `X ^ r - 1`) if `f (X) ^ m ≡ f (X ^ m)` modulo `X ^ r - 1`.
-/

namespace AKS

open Polynomial

variable {R : Type*} [CommRing R]

/-- `m` is introspective for `f` modulo `X ^ r - 1`. -/

lemma dvd_comp_of_cyclo_dvd {r m : ℕ} {g : R[X]} (h : (X ^ r - 1 : R[X]) ∣ g) :
    (X ^ r - 1 : R[X]) ∣ g.comp (X ^ m) := by
  obtain ⟨q, rfl⟩ := h
  rw [Polynomial.mul_comp]
  refine Dvd.dvd.mul_right ?_ _
  have h1 : ((X : R[X]) ^ r - 1).comp (X ^ m) = ((X : R[X]) ^ r) ^ m - 1 := by
    simp [← pow_mul, mul_comm]
  rw [h1]
  simpa using sub_dvd_pow_sub_pow ((X : R[X]) ^ r) 1 m

