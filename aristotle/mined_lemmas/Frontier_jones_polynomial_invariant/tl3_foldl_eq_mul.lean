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

theorem tl3_foldl_eq_mul (A B : R) (w : List Letter) (x : TL3 R) :
    w.foldl (fun x l => TL3.act A B l x) x = TL3.mul A B x (tl3 A B w) := by
  induction w generalizing x with
  | nil => simp [tl3, TL3.mul_one]
  | cons l w ih =>
      have h1 : (l :: w).foldl (fun x l => TL3.act A B l x) x
          = w.foldl (fun x l => TL3.act A B l x) (TL3.act A B l x) := by
        simp only [List.foldl_cons]
      have h2 : tl3 A B (l :: w) = TL3.mul A B (TL3.act A B l (TL3.one R)) (tl3 A B w) := by
        rw [tl3]
        simp only [List.foldl_cons]
        exact ih (TL3.act A B l (TL3.one R))
      rw [h1, ih (TL3.act A B l x), h2, TL3.act_eq_mul A B l x, TL3.mul_assoc]

