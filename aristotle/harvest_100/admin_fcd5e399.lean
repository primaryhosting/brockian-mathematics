import Mathlib
/-!
# Cantor No Surjection
Category: Frontier — Set Theory
Target: Infinity.cantor_no_surjection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- Key intermediate lemma: the diagonal set `{x | x ∉ f x}` is not in the range of `f`,
i.e. no `a : X` satisfies `f a = {x | x ∉ f x}`. -/
theorem diagonal_not_mem_range {X : Type*} (f : X → Set X) :
    {x : X | x ∉ f x} ∉ Set.range f := by
  rintro ⟨a, ha⟩
  have h : a ∈ f a ↔ a ∉ f a := by
    constructor
    · intro h
      have : a ∈ {x : X | x ∉ f x} := ha ▸ h
      exact this
    · intro h
      have h' : a ∈ {x : X | x ∉ f x} := h
      exact ha ▸ h'
  tauto

/-- **Cantor's theorem**: for any type `X`, no function `f : X → Set X` is surjective. -/
theorem cantor_no_surjection {X : Type*} (f : X → Set X) : ¬ Function.Surjective f := by
  intro hf
  exact diagonal_not_mem_range f (hf _)

/-- The same result, derived directly from Mathlib's `Function.cantor_surjective`. -/
theorem cantor_no_surjection' {X : Type*} (f : X → Set X) : ¬ Function.Surjective f :=
  fun hf => Function.cantor_surjective f hf

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

