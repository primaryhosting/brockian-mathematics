import Mathlib

/-!
# Cantor No Injection From Powerset
Category: Frontier — Set Theory
Target: Infinity.cantor_no_injection_from_powerset
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


namespace Infinity

/-- Key intermediate lemma: for every `g : Set X → X` there is a pair of distinct
sets sent to the same point. -/
theorem exists_ne_eq_of_powerset_map {X : Type*} (g : Set X → X) :
    ∃ A B : Set X, A ≠ B ∧ g A = g B := by
  by_contra h
  push_neg at h
  exact Function.cantor_injective g (fun A B hAB => by
    by_contra hne
    exact h A B hne hAB)

/-- Dual Cantor: no function `g : Set X → X` is injective. -/
theorem cantor_no_injection_from_powerset {X : Type*} (g : Set X → X) :
    ¬ Function.Injective g := by
  intro hg
  obtain ⟨A, B, hne, heq⟩ := exists_ne_eq_of_powerset_map g
  exact hne (hg heq)

end Infinity

