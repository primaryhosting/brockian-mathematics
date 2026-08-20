import Mathlib

/-!
# Cantor No Injection From Powerset
Category: Frontier — Set Theory
Target: Infinity.cantor_no_injection_from_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- **Dual Cantor theorem**: for any type `X`, no function `g : Set X → X` is injective.

This is exactly Mathlib's `Function.cantor_injective`, which derives it from
`Function.cantor_surjective` via the right inverse
`a ↦ {b | ∀ U, a = g U → U b}`. -/
theorem cantor_no_injection_from_powerset {X : Type*} (g : Set X → X) :
    ¬ Function.Injective g :=
  Function.cantor_injective g

/-- The diagonal set used in the self-contained proof below: the set of points of `X`
that are the `g`-image of some set not containing them. -/
def diagSet {X : Type*} (g : Set X → X) : Set X :=
  {x | ∃ U : Set X, g U = x ∧ x ∉ U}

/-- Self-contained diagonal proof of the dual Cantor theorem, not using
`Function.cantor_injective`: if `g : Set X → X` were injective, then `g (diagSet g)`
would belong to `diagSet g` if and only if it does not. -/
theorem cantor_no_injection_from_powerset' {X : Type*} (g : Set X → X) :
    ¬ Function.Injective g := by
  intro hg
  set A : Set X := diagSet g with hA
  set a : X := g A with ha
  have key : a ∈ A ↔ a ∉ A := by
    constructor
    · rintro ⟨U, hU, hUa⟩
      have : U = A := hg (hU.trans ha)
      exact this ▸ hUa
    · intro h
      exact ⟨A, ha.symm, h⟩
  exact (iff_not_self key).elim

/-- Consequence: there is no bijection between `Set X` and `X`. -/
theorem no_bijection_powerset {X : Type*} (g : Set X → X) :
    ¬ Function.Bijective g :=
  fun h => cantor_no_injection_from_powerset g h.1

end Infinity

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

