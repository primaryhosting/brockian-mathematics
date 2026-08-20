/-!
# Cantor Powerset
Category: Computer Science
Target: CS.cantor_powerset
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Cantor's theorem**: for every type `A`, no map from `A` to its powerset
`𝒫(A)` (represented as the type of predicates `A → Prop`) is surjective. -/

theorem cantor_powerset_set {A : Type u} (f : A → Set A) : ¬ Function.Surjective f := by
  intro hf
  refine cantor_powerset (fun a => fun x => x ∈ f a) ?_
  intro s
  obtain ⟨a, ha⟩ := hf {x | s x}
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

