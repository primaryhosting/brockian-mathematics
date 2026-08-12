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

namespace CS

/-- **Cantor's theorem**: for any type `A` there is no surjection from `A` onto its
powerset `Set A`. -/
theorem cantor_powerset {A : Type*} (f : A → Set A) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf {x : A | x ∉ f x}
  have : a ∈ f a ↔ a ∉ f a := by
    constructor
    · intro h
      have : a ∈ {x : A | x ∉ f x} := ha ▸ h
      exact this
    · intro h
      have : a ∈ {x : A | x ∉ f x} := h
      exact ha ▸ this
  tauto

end CS

