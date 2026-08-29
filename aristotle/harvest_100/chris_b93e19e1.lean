import Mathlib

/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- **Cantor–Schröder–Bernstein**: for types `X` and `Y`, if there is an injection `X → Y`
and an injection `Y → X`, then there is a bijection between `X` and `Y`, i.e. an
equivalence `X ≃ Y`. -/
theorem schroeder_bernstein {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Nonempty (X ≃ Y) :=
  Function.Embedding.antisymm ⟨f, hf⟩ ⟨g, hg⟩

/-- Restatement of Cantor–Schröder–Bernstein in terms of the existence of a bijective map. -/
theorem schroeder_bernstein_exists_bijective {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : X → Y, Function.Bijective h := by
  obtain ⟨e⟩ := schroeder_bernstein hf hg
  exact ⟨e, e.bijective⟩

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

