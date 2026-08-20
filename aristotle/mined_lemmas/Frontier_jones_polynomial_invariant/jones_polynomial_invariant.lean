import Mathlib
import RequestProject.Jones

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
# The Kauffman bracket / Jones polynomial of braid closures (3-strand case)

This file develops, from scratch, a concrete algebraic model of the Kauffman bracket
state sum for closures of braids on at most three strands, via the Temperley–Lieb
algebras `TL₂` and `TL₃`, and proves that the writhe-normalised bracket
(the Jones polynomial, up to the substitution `A = t^{-1/4}`) is invariant under the
Reidemeister moves that are visible in this setting:

* Reidemeister II  : cancelling a pair `σᵢ σᵢ⁻¹` (or `σᵢ⁻¹ σᵢ`) anywhere in the braid word;
* Reidemeister III : the braid relation `σ₁σ₂σ₁ = σ₂σ₁σ₂` (and its negative version);
* Reidemeister I   : Markov stabilisation, `closure (ι w · σ₂^{±1}) = closure w`.

Everything takes place over an arbitrary commutative ring `R` with two elements
`A B : R` satisfying `A * B = 1` (so `B = A⁻¹`), and `δ = -A² - B²` is the loop value.
-/

namespace Frontier

/-! ## The Temperley–Lieb algebra `TL₃` -/

/-- An element of the Temperley–Lieb algebra `TL₃` over `R`, written in the standard
diagram basis `1, e₁, e₂, e₁e₂, e₂e₁`. -/
@[ext]
structure TL3 (R : Type*) where
  c1 : R
  ce1 : R
  ce2 : R
  ce12 : R
  ce21 : R

/-- An element of the Temperley–Lieb algebra `TL₂` over `R`, written in the standard
diagram basis `1, e₁`. -/
@[ext]
structure TL2 (R : Type*) where
  c1 : R
  ce1 : R

variable {R : Type*} [CommRing R]

/-- The loop value `δ = -A² - A⁻²` of the Kauffman bracket. -/

theorem jones_polynomial_invariant (A B : R) (hAB : A * B = 1) :
    (∀ (i : Bool) (w₁ w₂ : List Letter),
        jones3 A B (w₁ ++ (i, true) :: (i, false) :: w₂) = jones3 A B (w₁ ++ w₂)) ∧
    (∀ (i : Bool) (w₁ w₂ : List Letter),
        jones3 A B (w₁ ++ (i, false) :: (i, true) :: w₂) = jones3 A B (w₁ ++ w₂)) ∧
    (∀ (s : Bool) (w₁ w₂ : List Letter),
        jones3 A B (w₁ ++ (false, s) :: (true, s) :: (false, s) :: w₂) =
          jones3 A B (w₁ ++ (true, s) :: (false, s) :: (true, s) :: w₂)) ∧
    (∀ w : List Bool, jones3 A B (incl w ++ [(true, true)]) = jones2 A B w) ∧
    (∀ w : List Bool, jones3 A B (incl w ++ [(true, false)]) = jones2 A B w) ∧
    (∀ w₁ w₂ : List Letter, jones3 A B (w₁ ++ w₂) = jones3 A B (w₂ ++ w₁)) :=
  ⟨fun i w₁ w₂ => jones3_R2_pos A B hAB i w₁ w₂,
   fun i w₁ w₂ => jones3_R2_neg A B hAB i w₁ w₂,
   fun s w₁ w₂ => jones3_R3 A B hAB s w₁ w₂,
   fun w => jones3_stab_pos A B hAB w,
   fun w => jones3_stab_neg A B hAB w,
   fun w₁ w₂ => jones3_conj A B w₁ w₂⟩

/-- The invariant is not constant: at the specialisation `A = 2` over `ℚ` it takes
different values on the trefoil (the closure of `σ₁³`) and on the unknot (the closure
of `σ₁`), so the theory above is not vacuous. -/
