/-!
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Cantor's theorem**: for every type `A`, no map from `A` to its powerset
`𝒫(A)` (represented by characteristic predicates `A → Prop`, which is definitionally
`Set A`) is surjective.

The header comment required for this file is a module docstring, which Lean requires
to precede any `import`; the statement and proof therefore use only Lean core notions.
A restatement in terms of Mathlib's `Set A` is given in
`RequestProject/CantorPowersetSet.lean`. -/
theorem cantor_powerset {A : Type u} (f : A → (A → Prop)) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf (fun x => ¬ f x x)
  have h : f a a ↔ ¬ f a a := by
    constructor
    · intro h
      have : (fun x => ¬ f x x) a := ha ▸ h
      exact this
    · intro h
      have : f a a = ¬ f a a := congrFun ha a
      exact this ▸ h
  have hn : ¬ f a a := fun hfa => h.mp hfa hfa
  exact hn (h.mpr hn)

end CS

import Mathlib
import RequestProject.CantorPowerset

/-!
# Cantor's theorem, stated with Mathlib's `Set`

Restatement of `CS.cantor_powerset` using Mathlib's powerset type `Set A`.
-/

namespace CS

/-- **Cantor's theorem**: there is no surjection `A → Set A`. -/
theorem cantor_powerset_set {A : Type u} (f : A → Set A) : ¬ Function.Surjective f :=
  cantor_powerset f

/-- **Cantor's theorem**, existential form: there is no surjection from `A` onto `𝒫(A)`. -/
theorem no_surjection_onto_powerset {A : Type u} :
    ¬ ∃ f : A → Set A, Function.Surjective f := by
  rintro ⟨f, hf⟩
  exact cantor_powerset_set f hf

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

