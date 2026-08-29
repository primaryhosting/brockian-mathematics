/-!
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The powerset of a type `A`, represented as the type of predicates on `A`
(equivalently, `Set A`). -/
abbrev Powerset (A : Type u) : Type u := A → Prop

/-- **Cantor's theorem**: for every type `A`, no map `A → 𝒫(A)` is surjective.

The proof is the classical diagonal argument: given `f : A → 𝒫(A)`, the
"diagonal" subset `D = {x | ¬ f x x}` is not in the image of `f`, since
`f a = D` would give the contradiction `f a a ↔ ¬ f a a`. -/
theorem cantor_powerset {A : Type u} (f : A → Powerset A) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf (fun x => ¬ f x x)
  have h : f a a ↔ ¬ f a a := Iff.of_eq (congrFun ha a)
  exact (fun h' => h.mp h' h') (h.mpr (fun h' => h.mp h' h'))

/-- Equivalent formulation: there is no surjection from `A` onto its powerset. -/
theorem no_surjection_onto_powerset (A : Type u) :
    ¬ ∃ f : A → Powerset A, Function.Surjective f := by
  rintro ⟨f, hf⟩
  exact cantor_powerset f hf

end CS

import Mathlib
import RequestProject.CantorPowerset

/-!
# Cantor's theorem, `Set`-valued form

A restatement of `CS.cantor_powerset` using Mathlib's `Set A` for the powerset.
-/

namespace CS

/-- **Cantor's theorem** in terms of `Set A`: no map `A → Set A` is surjective. -/
theorem cantor_powerset_set {A : Type u} (f : A → Set A) :
    ¬ Function.Surjective f := by
  intro hf
  refine cantor_powerset (fun a => fun x => x ∈ f a) ?_
  intro p
  obtain ⟨a, ha⟩ := hf {x | p x}
  exact ⟨a, by simp only [ha]; rfl⟩

end CS

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

