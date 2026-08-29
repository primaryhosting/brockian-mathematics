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

lemma intro_char_prime {p : ℕ} [Fact (Nat.Prime p)] (r : ℕ) (f : (ZMod p)[X]) :
    Intro r p f := by
  have hcomp : f.comp (X ^ p) = f ^ p := by
    rw [← Polynomial.expand_eq_comp_X_pow]
    have h := Polynomial.map_frobenius_expand (R := ZMod p) (p := p) (f := f)
    rw [ZMod.frobenius_zmod] at h
    simpa using h
  simp [Intro, hcomp]

end AKS

